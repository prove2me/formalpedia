-- Prove2me | Theorems.Thm_OAI_SLEExactGauge_RegularSLEPresentation_source_past_spatial_slab_finite_exponential
-- name    : OAI.SLEExactGauge.RegularSLEPresentation.source_past_spatial_slab_finite_exponential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T22:36:46.938009+00:00
-- url     : https://prove2.me/theorems/e0cab02c-d6f6-4f2a-be76-ffc4e78bea68
-- title:
--   OAI.SLEExactGauge.RegularSLEPresentation.source_past_spatial_slab_finite_exponential: intermediate lemma from OpenAI, An explicit exact Hausdorff gauge for SLE
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SLEExactGauge.sourceLowerMain_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit exact Hausdorff gauge for SLE*, OpenAI Math Release, September 26, 2026, result family 230, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SLEExactGauge.RegularSLEPresentation.source_past_spatial_slab_finite_exponential` of [lean/OAI/Probability/SLE/SmallKappaSausageMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SLE/SmallKappaSausageMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SLEExactGauge.RegularSLEPresentation`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology NNReal ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology NNReal`, `open Set Filter MeasureTheory Complex`, `open MeasureTheory ProbabilityTheory Set Filter`, `open Set Filter Metric Complex InnerProductSpace`, `open scoped Topology Laplacian`, `open Set Filter Metric Complex MeasureTheory`, `open Set Filter Metric Complex MeasureTheory InnerProductSpace`, `open scoped Topology Laplacian ENNReal`, `open scoped Topology ENNReal`, `open scoped Topology Laplacian RealInnerProductSpace`, `open Set Filter Metric Complex`, `open scoped Topology`, `open Set Filter Metric`, `open Set Filter MeasureTheory Metric`, `open Set Filter Complex`, `open scoped Topology ComplexConjugate NNReal`, `open scoped Topology ENNReal NNReal ComplexConjugate`, `open Set Filter Metric MeasureTheory Complex`, `open Set Filter MeasureTheory ProbabilityTheory Classical`, `open scoped Topology ENNReal NNReal`, `open Set Filter MeasureTheory ProbabilityTheory Metric Classical`, `open Set Filter`, `open scoped Topology NNReal ENNReal ComplexConjugate`, `open scoped ENNReal NNReal`, `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory ProbabilityTheory Metric`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   theorem source_past_spatial_slab_finite_exponential
--       (hκ : 0 < κ) (hκ4 : κ ≤ 4)
--       (A : Set ℂ) (hA : MeasurableSet A)
--       (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
--       (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
--       (S s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
--       (hbefore : ∀ ω ∈ D, ∀ z : A, s ≤ boundedSpatialHit (γ ω) z r S)
--       (θ : ℝ) :
--       (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal (Real.exp
--         (θ * (∫ z in A,
--           greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
--           greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z) -
--           θ^2 * slabVariance κ ε r A / 2)) else 1 ∂(P.comap Subtype.val)) ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.SLEExactGauge.RegularSLEPresentation`, `OAI.SLEExactGauge.boundedSpatialHit`, `OAI.SLEExactGauge.greenDensity`, `OAI.SLEExactGauge.slabVariance` and `OAI.SLEExactGauge.RegularSLEPresentation.filtration` (definitions bundle `OAIQ27Sle000` of this split).
--
--   **Used by.** The proof of `OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa` of this split imports it.
-- source:
--   OpenAI, An explicit exact Hausdorff gauge for SLE, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 230; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SLE/SmallKappaSausageMoments.lean (declaration OAI.SLEExactGauge.RegularSLEPresentation.source_past_spatial_slab_finite_exponential)

import Mathlib
import Definitions.Def_OAIQ27Sle000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_slab_finite_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (S s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z : A, s ≤ boundedSpatialHit (γ ω) z r S)
    (θ : ℝ) :
    (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal (Real.exp
      (θ * (∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z) -
        θ^2 * slabVariance κ ε r A / 2)) else 1 ∂(P.comap Subtype.val)) ≤ 1 := by
  sorry

end RegularSLEPresentation
end
end SLEExactGauge
end

end
end
end

end OAI
end
