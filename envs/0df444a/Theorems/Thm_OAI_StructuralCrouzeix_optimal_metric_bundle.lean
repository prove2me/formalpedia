-- Prove2me | Theorems.Thm_OAI_StructuralCrouzeix_optimal_metric_bundle
-- name    : OAI.StructuralCrouzeix.optimal_metric_bundle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:26.878922+00:00
-- url     : https://prove2.me/theorems/24afb7d3-1aa5-4c5c-b293-41b0d9f6379a
-- title:
--   OAI.StructuralCrouzeix.optimal_metric_bundle: intermediate lemma from OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StructuralCrouzeixReference.challenge`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StructuralCrouzeix.optimal_metric_bundle` of [lean/OAI/Analysis/StructuralCrouzeix/OptimizerAssembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StructuralCrouzeix/OptimizerAssembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StructuralCrouzeix`, with `open Set Filter Metric Complex MeasureTheory`, `open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder`, `open CompleteCrouzeix`):
--
--   ```lean
--   theorem optimal_metric_bundle (D : AdmissibleDomain)
--       {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
--       (hW : numericalRange A ⊆ D.domain) :
--       let T := matrixAnalyticEval A D.interior.toDisk
--       StrictlyFeasible T ∧
--       ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ 2 ∧
--         (∃ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H) ∧
--         ∀ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H →
--           let S := CFC.sqrt H
--           let A' := S*A*S⁻¹
--           let B := S*T*S⁻¹
--           H.PosDef ∧ IsUnit S ∧
--           B = matrixAnalyticEval A' D.interior.toDisk ∧
--           Bᴴ*B ≤ 1 ∧ spectralRadius ℂ B < 1 ∧
--           ‖S‖*‖S⁻¹‖ = κ ∧
--           (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R →
--             (R*T*R⁻¹)ᴴ*(R*T*R⁻¹) ≤ 1 → κ ≤ ‖R‖*‖R⁻¹‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CompleteCrouzeix.AdmissibleDomain` (definitions bundle `OAIW2SC000` of this split); `OAI.CompleteCrouzeix.matrixAnalyticEval`, `OAI.CompleteCrouzeix.numericalRange`, `OAI.StructuralCrouzeix.IsMinimizing`, `OAI.StructuralCrouzeix.StrictlyFeasible` and `OAI.CompleteCrouzeix.DiskCoordinate` (the published bundle `Def_StructuralCrouzeix`).
--
--   **Used by.** The proof of `OAI.StructuralCrouzeixReference.challenge` of this split imports it.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StructuralCrouzeix/OptimizerAssembly.lean (declaration OAI.StructuralCrouzeix.optimal_metric_bundle)

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

theorem optimal_metric_bundle (D : AdmissibleDomain)
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain) :
    let T := matrixAnalyticEval A D.interior.toDisk
    StrictlyFeasible T ∧
    ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ 2 ∧
      (∃ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H) ∧
      ∀ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H →
        let S := CFC.sqrt H
        let A' := S*A*S⁻¹
        let B := S*T*S⁻¹
        H.PosDef ∧ IsUnit S ∧
        B = matrixAnalyticEval A' D.interior.toDisk ∧
        Bᴴ*B ≤ 1 ∧ spectralRadius ℂ B < 1 ∧
        ‖S‖*‖S⁻¹‖ = κ ∧
        (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R →
          (R*T*R⁻¹)ᴴ*(R*T*R⁻¹) ≤ 1 → κ ≤ ‖R‖*‖R⁻¹‖) := by
  sorry

end StructuralCrouzeix
end

end OAI
end
