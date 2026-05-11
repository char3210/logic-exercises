

structure Signature where
  Γ : Type
  Γa : Γ → Nat
  Δ : Type
  Δa : Δ → Nat

universe u

inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

def head {α} : {n : Nat} → Vect α (n+1) → α
  | _n, .cons a _as => a

def tail {α} : {n : Nat} → Vect α (n+1) → Vect α n
  | _n, .cons _a as => as

def destr_2 {α} : Vect α 2 → α × α
  | .cons a (.cons b .nil) => (a, b)

def Vect.map {α β n} (f : α → β) (v : Vect α n) : Vect β n :=
  match v with
  | .nil => nil
  | .cons a rest => cons (f a) (Vect.map f rest)

structure Struct (S : Signature) where
  U : Type
  iΓ : (f : S.Γ) → Vect U (S.Γa f) → U
  iΔ : (r : S.Δ) → Vect U (S.Δa r) → Prop


structure StructHom {S: Signature} (A: Struct S) (B: Struct S) where
  toFun : A.U → B.U
  preserveF : ∀ (f : S.Γ) (args : Vect A.U (S.Γa f)),
    toFun (A.iΓ f args) = B.iΓ f (Vect.map toFun args)
  preserveR : ∀ (r : S.Δ) (args : Vect A.U (S.Δa r)),
    A.iΔ r args → B.iΔ r (Vect.map toFun args)

structure StructEmbedding {S: Signature} (A: Struct S) (B: Struct S)
extends StructHom A B where
  inj : Function.Injective toFun
  reflectR : ∀ (r : S.Δ) (args : Vect A.U (S.Δa r)),
    B.iΔ r (Vect.map toFun args) → A.iΔ r args

structure StructIso {S: Signature} (A: Struct S) (B: Struct S) where
  fw : StructHom A B
  bw : StructHom B A
  a_comp_id : bw.toFun ∘ fw.toFun = id
  b_comp_id : fw.toFun ∘ bw.toFun = id

theorem vect_map_comp {A B C n} (f : A → B) (g : B → C) (v : Vect A n) : Vect.map g (Vect.map f v) = Vect.map (g ∘ f) v := by
  induction v with
  | nil => simp [Vect.map]
  | cons a r h => simp [Vect.map, h]

theorem Vect.map_id : Vect.map id v = v := by
  induction v
  simp [map]
  simp [map]
  assumption

theorem surj_emb_of_iso {S} {A B : Struct S} (φ : StructIso A B) :
∃ (f : StructEmbedding A B), f.toFun = φ.fw.toFun ∧ Function.Surjective f.toFun := by
  refine ⟨⟨φ.fw, ?_, ?_⟩, ?_⟩
  · unfold Function.Injective
    intros a1 a2 h
    have h1 := congrArg φ.bw.toFun h
    change (_ ∘ _) a1 = (_ ∘ _) a2 at h1
    rw [φ.a_comp_id] at h1
    exact h1
  · intros r args h
    have h1 := φ.bw.preserveR r (Vect.map φ.fw.toFun args) h
    rw [vect_map_comp, φ.a_comp_id, Vect.map_id] at h1
    exact h1
  · simp
    unfold Function.Surjective
    intro b
    exists φ.bw.toFun b
    change (_ ∘ _) _ = _
    rw [φ.b_comp_id]
    rfl

set_option pp.proofs true

theorem iso_of_surj_emb (f : StructEmbedding A B) (fsurj : Function.Surjective f.toFun) :
  ∃ (f' : StructIso A B), f'.fw = f.toStructHom := by
  unfold Function.Surjective at fsurj
  -- i know choose can do this this is an exercise in my type theory knowledge
  let g : B.U → A.U := fun b => (fsurj b).choose
  have hfg (x) : f.toFun (g x) = x := by
    have h := Exists.choose_spec (fsurj x)
    exact h
  have hfg' : f.toFun ∘ g = id := by ext; apply hfg
  have hgf (x) : g (f.toFun x) = x := by
    have h := Exists.choose_spec (fsurj (f.toFun x))
    simp [g]
    apply f.inj
    exact h
  have hgf' : g ∘ f.toFun = id := by ext; apply hgf
  -- i guess i shouldn't torture myself by using axiom choice
  refine ⟨⟨f.toStructHom, ?_, ?_, ?_⟩, rfl⟩
  apply StructHom.mk g
  intros fn args
  -- g (fn^B ...) = fn^A (g ..., g ...)
  have h1 := f.preserveF fn (Vect.map g args)
  rw [vect_map_comp, hfg', Vect.map_id] at h1
  have h2 := congrArg g h1
  rw [hgf] at h2
  simp [h2]

  intros r args hbr
  have h1 := f.reflectR r (Vect.map g args)
  rw [vect_map_comp, hfg', Vect.map_id] at h1
  exact h1 hbr

  simp [hgf']
  simp [hfg']

-- example
inductive LOGFun where
  | id
  | op

def LOGFunA : LOGFun → Nat
  | .id => 0
  | .op => 2

inductive LOGRel where
  | lt

def LOGRelA : LOGRel → Nat
  | .lt => 2

def LOG : Signature :=
  Signature.mk LOGFun LOGFunA LOGRel LOGRelA

def NatLOG : Struct LOG :=
  Struct.mk Nat
  (fun
  | .id => (fun .nil => 0)
  | .op => (fun e => let (a, b) := destr_2 e; a + b))
  (fun
  | .lt => (fun e => let (a, b) := destr_2 e; a ≤ b))
