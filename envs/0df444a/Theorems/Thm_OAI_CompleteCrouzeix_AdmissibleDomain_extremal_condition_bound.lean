-- Prove2me | Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_extremal_condition_bound
-- name    : OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:11.971886+00:00
-- url     : https://prove2.me/theorems/04c26ee7-8014-41d3-836d-72f628830558
-- title:
--   OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound: intermediate lemma from OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StructuralCrouzeixReference.challenge`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound` of [lean/OAI/Analysis/NumericalRange/DensityComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/DensityComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CompleteCrouzeix.AdmissibleDomain`, with `open Set Filter Metric Complex MeasureTheory`, `open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker`):
--
--   ```lean
--   theorem extremal_condition_bound (A : Matrix (Fin n) (Fin n) ℂ)
--       (hW : numericalRange A ⊆ D.domain)
--       {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
--       (hc : (matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk)ᴴ *
--         matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk ≤ 1)
--       {κ : ℝ} (hκ : 0 < κ) {X Y : Matrix (Fin n) (Fin m) ℂ}
--       (hX : S*X = (κ:ℂ) • X) (hY : S*Y = Y)
--       (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1) (hXY : Xᴴ*Y = 0)
--       {F : ℂ → Matrix (Fin m) (Fin m) ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
--       (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
--       (he : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
--         (completeAnalyticEval (S*A*S⁻¹) F) (vectorize X) = vectorize Y) : κ ≤ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CompleteCrouzeix.AdmissibleDomain` and `OAI.CompleteCrouzeix.vectorize` (definitions bundle `OAIW2SC000` of this split); `OAI.CompleteCrouzeix.completeAnalyticEval`, `OAI.CompleteCrouzeix.matrixAnalyticEval`, `OAI.CompleteCrouzeix.numericalRange` and `OAI.CompleteCrouzeix.DiskCoordinate` (the published bundle `Def_StructuralCrouzeix`).
--
--   **Used by.** The proof of `OAI.StructuralCrouzeix.optimal_metric_bundle` of this split imports it.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/DensityComparison.lean (declaration OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound)

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_257

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n m : ℕ} [Nonempty (Fin n)]

theorem extremal_condition_bound (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain)
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (hc : (matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk)ᴴ *
      matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hX : S*X = (κ:ℂ) • X) (hY : S*Y = Y)
    (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1) (hXY : Xᴴ*Y = 0)
    {F : ℂ → Matrix (Fin m) (Fin m) ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
    (he : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (completeAnalyticEval (S*A*S⁻¹) F) (vectorize X) = vectorize Y) : κ ≤ 2 := by
  sorry
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end
