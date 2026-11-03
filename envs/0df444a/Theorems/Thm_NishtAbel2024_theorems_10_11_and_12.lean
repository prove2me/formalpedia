-- Prove2me | Theorems.Thm_NishtAbel2024_theorems_10_11_and_12
-- name    : NishtAbel2024.theorems_10_11_and_12
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-10-31T19:06:18.485248+00:00
-- url     : https://prove2.me/theorems/b43339d8-647a-4962-ba44-0b270f6a5742
-- title:
--   Constraint Orientation in CompareTypes (Theorem 10) and Bipartiteness of Call-Site Constraint Graphs (Theorems 11 & 12)
-- statement:
--   Theorems 10, 11, and 12 (Section 6.3, pp. 52–56): (1) every constraint mentioning a polarized size variable `i` in `CompareTypes Φ Δ ι π A C Cs` is oriented according to `a ≤^{π π' π''} i`; (2) `InferTerm` and `CheckTerm` preserve fixpoint polarity invariants and emit no constraint from a flexible variable to a tracked variable `i ∈ X`; and (3) across any encoded copattern clause body, no constraint has a flexible variable on the LHS and a rigid variable on the RHS.
--
--   **Superseded.** This is the first formalization of Theorems 10–12 (pp. 52–56) of
--   the thesis. It is refuted through its Theorem 11 conjunct by the disproof
--   `66d9f635-be98-4efa-83f1-846d677c4882`. A positive rigid size variable $i$ occurs twice in the
--   type $\nu^i\{d_0 : \mu^i\{\}\}$ of a variable $x$, inside a least fixpoint and
--   also at the outer greatest fixpoint. The statement's hypotheses check only one
--   occurrence and accept this. Inferring the projection $x.d_0$ then emits a
--   constraint $j < i$ with a fresh flexible variable $j$, which Theorem 11 forbids.
--   The thesis requires that, for positive polarity, all occurrences of a rigid
--   variable lie in least fixpoints (§6.3.4), so this is a missing hypothesis, not a
--   counterexample to the thesis. Corrected statement:
--   `NishtAbel2024V2.theorems_10_11_and_12`. It concerns the instrumented judgments
--   `GuardedCompareTypes`, `SafeInferTerm` and `SafeCheckTerm`, which track size
--   occurrences explicitly.
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Section 6.3, Theorem 10 (p. 52), Theorem 11 (pp. 54–55), and Theorem 12 (p. 56).

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

/-- Theorem 10 (Polarities in type comparison, pp. 52–53),
Theorem 11 (Nature of rigid variables, pp. 53–54), and
Theorem 12 (Rigid variables in constraints, pp. 55–56):
1. (**Theorem 10**) Under `FlexPolHygiene`, if `(i, π') ∈ Φ` (`π' ∈ {+, −}`) occurs in `C` only
   with polarity `π'' ∈ {+, −}` (and not in `A`), then in `Φ; Δ; ι ⊢_{SCT} A ≤^π C ⇒ Cs`, every
   constraint in `Cs` mentioning `i` has the polarized form `a ≤^{π π' π''} i`.
2. (**Theorem 11**) Under `RigidVarHypotheses π X Φ₀ Γ Δ A`, neither call-site inference nor
   call-site checking generates a constraint `(j R i) ∈ Cs` with flexible `j ∈ Φ \ X` and rigid
   `i ∈ X`; in inference mode, every `i ∈ X` either occurs in the inferred type `C` with polarity
   `π` or does not occur in `C`.
3. (**Theorem 12**) For any clause body checked after signature encoding and copattern-spine
   matching, no constraint `(k R j) ∈ Cs` has a flexible variable `k ∈ Φ \ (Ψ₁ ++ Ψ₂)` on the LHS
   and a rigid variable `j ∈ Ψ₁ ++ Ψ₂` on the RHS. -/
theorem theorems_10_11_and_12 :
    (∀ (Φ : FlexVars) (Δ : KindingCtx) (ι : SKind) (π π' π'' : Polarity)
       (A C : TypeExpr) (Cs : List SizeConstraint) (i : SizeVar),
      FlexPolHygiene Φ Δ A C →
      Φ.lookupPol i = some π' →
      (π' = .pos ∨ π' = .neg) →
      (π'' = .pos ∨ π'' = .neg) →
      ¬ SizeOccursIn i A →
      (∀ fk π₀, SizeOccursFixPol Δ fk i π₀ C →
        π₀ = π'' ∧ ((fk = .mu ∧ π' = .pos) ∨ (fk = .nu ∧ π' = .neg))) →
      CompareTypes Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (π : Polarity) (X : List SizeVar)
       (Φ₀ Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (A C : TypeExpr)
       (t t' : Term) (Cs : List SizeConstraint) (T : List SizeVar),
      RigidVarHypotheses π X Φ₀ Γ Δ A →
      ((InferTerm sig Ξ Φ₀ Γ Δ t C Φ Cs T t' →
          (∀ i ∈ X, ∀ j ∈ Φ.dom, j ∉ X →
            ∀ c ∈ Cs, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)) ∧
          (∀ i ∈ X,
            SizeOccursFixPol Δ (if π == .pos then .mu else .nu) i π C ∨ ¬ SizeOccursIn i C)) ∧
       (CheckTerm sig Ξ Φ₀ Γ Δ A t Φ Cs T t' →
          ∀ i ∈ X, ∀ j ∈ Φ.dom, j ∉ X →
            ∀ c ∈ Cs, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)))) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      ∀ k ∈ Φ.dom, k ∉ (Ψ₁ ++ Ψ₂).dom →
        ∀ j ∈ (Ψ₁ ++ Ψ₂).dom,
          ∀ c ∈ Cs, ¬ (c.lhs = .var k 0 ∧ c.rhs = .var j 0)) := by
  sorry

end NishtAbel2024
