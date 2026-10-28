-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_compact_sobolev_entropy_subdifferential
-- name    : OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:40:49.452961+00:00
-- url     : https://prove2.me/theorems/596fec55-c05a-400f-9a69-58ac5e6978aa
-- title:
--   OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Sobolev/SobolevSubdifferential.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Sobolev/SobolevSubdifferential.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction`):
--
--   ```lean
--   theorem RCD.compact_sobolev_entropy_subdifferential {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
--       (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
--       {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
--       (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
--       (o : X) (R : ℝ≥0)
--       (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
--       (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
--       {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
--       ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
--         IsTestPlan m (π:Measure (Curve X)) ∧ BoundedTracks (π:Measure (Curve X)) ∧
--         (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
--         IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
--         LipschitzWith (2*(R+2)) φ ∧ LipschitzWith (2*(R+2)) ψ ∧
--         (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
--         (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
--           dist (γ timeZero) (γ timeOne)^2/2) ∧
--         entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
--           ∫ x,2*w x*gamma m φ w x ∂m
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.entropyReal` and `OAI.WeakHessian.planEnergy` (definitions bundle `OAIQ52Wh000` of this split); `OAI.WeakHessian.squareDensityMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.BoundedTracks`, `OAI.WeakHessian.Curve`, `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.IsGeodesic`, `OAI.WeakHessian.IsOptimalCoupling`, `OAI.WeakHessian.IsTestPlan`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev`, `OAI.WeakHessian.Time`, `OAI.WeakHessian.curveMeasurableSpace`, `OAI.WeakHessian.endpointCoupling`, `OAI.WeakHessian.gamma`, `OAI.WeakHessian.timeOne` and `OAI.WeakHessian.timeZero` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.RCD.generator_entropy_subdifferential` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Sobolev/SobolevSubdifferential.lean (declaration OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh000
import Definitions.Def_OAIQ52Wh002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile22
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m]

theorem RCD.compact_sobolev_entropy_subdifferential {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      IsTestPlan m (π:Measure (Curve X)) ∧ BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      LipschitzWith (2*(R+2)) φ ∧ LipschitzWith (2*(R+2)) ψ ∧
      (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  sorry
end WeakHessian

end
end InlinedFile22

end OAI
end
