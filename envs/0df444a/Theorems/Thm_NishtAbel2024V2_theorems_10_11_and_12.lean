-- Prove2me | Theorems.Thm_NishtAbel2024V2_theorems_10_11_and_12
-- name    : NishtAbel2024V2.theorems_10_11_and_12
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T21:45:50.918004+00:00
-- url     : https://prove2.me/theorems/b11ab2f6-6f76-4d60-a538-8c10ccdc97d6
-- title:
--   Repaired V2 Constraint Orientation in GuardedCompareTypes (Theorem 10) and No-Incoming-Edge Invariants for SafeInferTerm/SafeCheckTerm (Theorems 11 & 12)
-- statement:
--   Repaired V2 formulation of Theorem 10 (pp. 52–53), Theorem 11 (pp. 53–54), and Theorem 12 (pp. 55–56) in `NishtAbel2024V2`: establishes polarized constraint orientation for `GuardedCompareTypes`, erasure and `NoDistinctIncoming` for `SafeInferTerm`/`SafeCheckTerm`, and `NoOutsideIncoming` for checked clause bodies.
--
--   **Differences from the thesis.** Theorems 10–12 concern instrumented versions of type comparison and term inference that track size occurrences explicitly (`GuardedCompareTypes`, `SafeInferTerm`, `SafeCheckTerm`; the last two erase to `InferTerm` and `CheckTerm`). This statement replaces the refuted `NishtAbel2024.theorems_10_11_and_12`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-- Repaired Theorem10 (Polarities in type comparison, pp. 52–53),
Theorem 11 (No incoming edges in guarded call-site inference/checking, pp. 53–54), and
Theorem 12 (No incoming flexible-to-rigid edges in clause bodies, pp. 55–56) in `NishtAbel2024V2`:
1. (**Theorem 10**) Under `FlexPolHygiene`, if `(i, π') ∈ Φ` (`π' ∈ {+, −}`) occurs in `C` only
   with polarity `π'' ∈ {+, −}` (and not in `A`), then in `GuardedCompareTypes i Φ Δ ι π A C Cs`,
   every constraint in `Cs` mentioning `i` has the polarized form `a ≤^{π π' π''} i`.
2. (**Theorem 11**) `SafeInferTerm` and `SafeCheckTerm` erase to `InferTerm` and `CheckTerm` and
   guarantee `NoDistinctIncoming i Cs` on all emitted constraints.
3. (**Theorem 12**) For any clause body checked via `SafeCheckTerm` after signature encoding and
   copattern-spine matching, every rigid variable `j ∈ (Ψ₁ ++ Ψ₂).dom` satisfies
   `NoOutsideIncoming (Ψ₁ ++ Ψ₂).dom j Cs`. -/
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
      GuardedCompareTypes i Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar)
       (Φ₀ Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (A C : TypeExpr)
       (t t' : Term) (Cs : List SizeConstraint) (T : List SizeVar),
      (SafeInferTerm sig Ξ i Φ₀ Γ Δ t C Φ Cs T t' →
        InferTerm sig Ξ Φ₀ Γ Δ t C Φ Cs T t' ∧ NoDistinctIncoming i Cs) ∧
      (SafeCheckTerm sig Ξ i Φ₀ Γ Δ A t Φ Cs T t' →
        CheckTerm sig Ξ Φ₀ Γ Δ A t Φ Cs T t' ∧ NoDistinctIncoming i Cs)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar) (j : SizeVar),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      j ∈ (Ψ₁ ++ Ψ₂).dom →
      SafeCheckTerm sig Ξ j ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      NoOutsideIncoming (Ψ₁ ++ Ψ₂).dom j Cs) := by
  sorry

end NishtAbel2024V2
