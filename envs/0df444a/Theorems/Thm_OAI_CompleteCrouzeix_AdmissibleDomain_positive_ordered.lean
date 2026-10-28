-- Prove2me | Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_positive_ordered
-- name    : OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:04.432993+00:00
-- url     : https://prove2.me/theorems/c00d0adf-31a6-48b1-bca1-2ced040ab839
-- title:
--   OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered: intermediate lemma from OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StructuralCrouzeixReference.challenge`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered` of [lean/OAI/Analysis/NumericalRange/OrderedDensities.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/OrderedDensities.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CompleteCrouzeix.AdmissibleDomain`, with `open Set Filter Metric Complex MeasureTheory`, `open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker`):
--
--   ```lean
--   lemma positive_ordered [Nonempty n] (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
--       (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
--       {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
--       (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
--       {X Y : Matrix n m ℂ} (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1)
--       (he : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (completeAnalyticEval A F)
--         (vectorize X) = vectorize Y) :
--       ∀ᵐ t ∂AddCircle.haarAddCircle,
--         weightedDensity (D.positiveDensity A hA t) X X = (D.trace F hF t)ᴴ * weightedDensity (D.positiveDensity A hA t) X Y ∧
--         weightedDensity (D.positiveDensity A hA t) X Y = D.trace F hF t * weightedDensity (D.positiveDensity A hA t) X X ∧
--         weightedDensity (D.positiveDensity A hA t) Y Y = weightedDensity (D.positiveDensity A hA t) X Y * (D.trace F hF t)ᴴ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CompleteCrouzeix.AdmissibleDomain`, `OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_56`, `OAI.CompleteCrouzeix.vectorize`, `OAI.CompleteCrouzeix.weightedDensity`, `OAI.CompleteCrouzeix.AdmissibleDomain.positiveDensity` and `OAI.CompleteCrouzeix.AdmissibleDomain.trace` (definitions bundle `OAIW2SC000` of this split); `OAI.CompleteCrouzeix.completeAnalyticEval`, `OAI.CompleteCrouzeix.matrixAnalyticEval` and `OAI.CompleteCrouzeix.DiskCoordinate` (the published bundle `Def_StructuralCrouzeix`).
--
--   **Used by.** The proof of `OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound` of this split imports it.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/OrderedDensities.lean (declaration OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered)

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_255} {m : Type u_256} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_56
lemma positive_ordered [Nonempty n] (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
    {X Y : Matrix n m ℂ} (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1)
    (he : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (completeAnalyticEval A F)
      (vectorize X) = vectorize Y) :
    ∀ᵐ t ∂AddCircle.haarAddCircle,
      weightedDensity (D.positiveDensity A hA t) X X = (D.trace F hF t)ᴴ * weightedDensity (D.positiveDensity A hA t) X Y ∧
      weightedDensity (D.positiveDensity A hA t) X Y = D.trace F hF t * weightedDensity (D.positiveDensity A hA t) X X ∧
      weightedDensity (D.positiveDensity A hA t) Y Y = weightedDensity (D.positiveDensity A hA t) X Y * (D.trace F hF t)ᴴ := by
  sorry
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end
