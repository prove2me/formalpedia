-- Prove2me | Theorems.Thm_NishtAbel2024V2_theorems_13_and_14
-- name    : NishtAbel2024V2.theorems_13_and_14
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T21:46:08.455682+00:00
-- url     : https://prove2.me/theorems/407e13f5-0b84-4863-9cf7-fd996a351787
-- title:
--   Repaired V2 Postchecked Clause Run Soundness (Theorem 13), Checked Constraint Solver Coherence (Theorem 14), and Postchecked Algorithm 2 Block Typing
-- statement:
--   Repaired V2 formulation of Theorem 13 (pp. 56–57), Theorem 14 (p. 58), and Corollary (p. 58) in `NishtAbel2024V2`: establishes target `ClauseCheck` for `PostcheckedAlgorithm2ClauseRun`, `CoherentSubst` for `CheckedConstraintSolver.checkedSolve`, and `MutualBlockTyping` for `PostcheckedAlgorithm2Accepts`.
--
--   **Differences from the thesis.** This statement is weaker than the thesis's Theorems 13–14. Theorem 13 takes the type check of each size-instantiated clause body as a hypothesis (`PostcheckedAlgorithm2ClauseRun`, a final check added to Algorithm 2), and Theorem 14 concerns `CheckedConstraintSolver.checkedSolve`, which returns Algorithm 1's substitution only when a finite coherence certificate succeeds. That inference always produces well-typed output from a well-formed signature is not stated here. This statement replaces the refuted `NishtAbel2024.theorems_13_and_14`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-- Repaired Theorem13 (Postchecked clause run typing soundness, pp. 56–57),
Theorem 14 (Soundness of the checked constraint solver, p. 58), and
Corollary (Target mutual-block typing of postchecked Algorithm 2, p. 59) in `NishtAbel2024V2`:
1. (**Theorem 13**) Every `PostcheckedAlgorithm2ClauseRun` elaborates its copattern spine and
   verifies that the size-instantiated clause `D' = {q⃗' → φ*(t')}` satisfies target `ClauseCheck`.
2. (**Theorem 14**) Whenever `CheckedConstraintSolver.checkedSolve fuel Ψ C T = some φ`, the
   returned substitution `φ` satisfies `CoherentSubst Ψ C φ`.
3. (**Corollary**) Whenever `PostcheckedAlgorithm2Accepts sig Ξ Ξannot` holds, the produced
   size-annotated mutual block `Ξannot` is well-typed in System `F_ω^{cop, SCT}`
   (`MutualBlockTyping sig Ξannot`). -/
theorem theorems_13_and_14 :
    (∀ (sig : GlobalSig) (Ξannot : MutualBlock) (𝒢 : InvGraphFamily) (caller : FunName)
       (Ψ₁ : SizeCtx) (A' : TypeExpr) (qs : PatSpine) (t : Term) (D' : Clause),
      Nonempty (PostcheckedAlgorithm2ClauseRun sig Ξannot 𝒢 caller Ψ₁ A' qs t D') →
      ClauseCheck ⟨sig, Ξannot, 𝒢, caller, Ψ₁⟩ (KindingCtx.empty.extSizes Ψ₁) [] D' A') ∧
    (∀ (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) (φ : FlexSubst),
      CheckedConstraintSolver.checkedSolve fuel Ψ C T = some φ →
      CoherentSubst Ψ C φ) ∧
    (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock),
      PostcheckedAlgorithm2Accepts sig Ξ Ξannot →
      MutualBlockTyping sig Ξannot) := by
  sorry

end NishtAbel2024V2
