-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_curvature_continuousOn
-- name    : OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:52:40.520487+00:00
-- url     : https://prove2.me/theorems/deaf6c8d-1b7e-44f4-b84f-c0c1621d2f38
-- title:
--   OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn` of [lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatCurvatureContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatCurvatureContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma RCD.weighted_heat_curvature_continuousOn {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
--       (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
--       (h : QuadraticCheegerEnergy (exponentialMeasure m V))
--       {f Af : Lp ℝ 2 (exponentialMeasure m V)} (ξ : Lp ℝ 2 (exponentialMeasure m V))
--       (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
--       {Cf CAf : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf)
--       (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
--       (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
--       {k : X → ℝ} (hkm : AEStronglyMeasurable k (exponentialMeasure m V))
--       {B : ℝ} (hkb : ∀ᵐ x ∂exponentialMeasure m V,|k x| ≤ B) (T : ℝ) :
--       ContinuousOn (fun s => ∫ x,(cheegerHeat h s ξ x*k x)*
--         gamma (exponentialMeasure m V) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
--           ∂exponentialMeasure m V) (Icc 0 T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.exponentialMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.IsFormGenerator` (definitions bundle `OAIQ52Wh004` of this split); `OAI.WeakHessian.cheegerHeat` and `OAI.WeakHessian.cheeger_closedQuadraticEnergy` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.cheegerEnergy` and `OAI.WeakHessian.gamma` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatCurvatureContinuity.lean (declaration OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile198
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_curvature_continuousOn {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {f Af : Lp ℝ 2 (exponentialMeasure m V)} (ξ : Lp ℝ 2 (exponentialMeasure m V))
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf CAf : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf)
    (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k (exponentialMeasure m V))
    {B : ℝ} (hkb : ∀ᵐ x ∂exponentialMeasure m V,|k x| ≤ B) (T : ℝ) :
    ContinuousOn (fun s => ∫ x,(cheegerHeat h s ξ x*k x)*
      gamma (exponentialMeasure m V) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m V) (Icc 0 T) := by
  sorry
end WeakHessian

end
end InlinedFile198

end OAI
end
