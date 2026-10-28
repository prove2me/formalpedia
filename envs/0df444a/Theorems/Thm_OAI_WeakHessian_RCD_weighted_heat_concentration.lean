-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_concentration
-- name    : OAI.WeakHessian.RCD.weighted_heat_concentration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:53:36.724629+00:00
-- url     : https://prove2.me/theorems/2702fa36-01e9-431c-a16c-9a0ac39845cf
-- title:
--   OAI.WeakHessian.RCD.weighted_heat_concentration: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.weighted_heat_concentration` of [lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatConcentration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatConcentration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma RCD.weighted_heat_concentration {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
--       (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       {F : X → ℝ} (hF : Continuous F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
--       {a : ℝ} (ha : 0 ≤ a)
--       (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
--       (u : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
--       (hun : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u x)
--       (hum : ∫ x,u x ∂exponentialMeasure m (fun x => a*F x) = 1)
--       {Bu : ℝ} (hBu : 0 ≤ Bu) (hub : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|u x| ≤ Bu)
--       {r : ℝ} (hr : 0 ≤ r)
--       (hs : ∀ᵐ x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) u,dist x o ≤ r)
--       {B : ℝ≥0} (hB : 0 < B)
--       (hcap : densityMeasure (exponentialMeasure m (fun x => a*F x)) u ≤ (B:ℝ≥0∞) • m)
--       {c : ℝ} (hc : 0 < c) (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
--       {T : ℝ} (hT : 0 ≤ T) :
--       ∃ μ : ProbabilityMeasure X,(μ:Measure X) = densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u) ∧
--         FiniteEntropy m (μ:Measure X) ∧ Integrable (fun x => dist x o) (μ:Measure X) ∧
--         (∫ x,dist x o ∂(μ:Measure X))^2 ≤
--           4*r^2+8*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1)+
--             16*(T*a)*CF+16*T^2*c^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.FiniteEntropy` (definitions bundle `OAIQ52Wh000` of this split); `OAI.WeakHessianTransport.densityMeasure` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.exponentialMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.cheegerHeat` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy` and `OAI.WeakHessian.RCD` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.every_geodesic` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatConcentration.lean (declaration OAI.WeakHessian.RCD.weighted_heat_concentration)

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

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_concentration {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {F : X → ℝ} (hF : Continuous F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hun : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m (fun x => a*F x) = 1)
    {Bu : ℝ} (hBu : 0 ≤ Bu) (hub : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|u x| ≤ Bu)
    {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ᵐ x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) u,dist x o ≤ r)
    {B : ℝ≥0} (hB : 0 < B)
    (hcap : densityMeasure (exponentialMeasure m (fun x => a*F x)) u ≤ (B:ℝ≥0∞) • m)
    {c : ℝ} (hc : 0 < c) (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ProbabilityMeasure X,(μ:Measure X) = densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u) ∧
      FiniteEntropy m (μ:Measure X) ∧ Integrable (fun x => dist x o) (μ:Measure X) ∧
      (∫ x,dist x o ∂(μ:Measure X))^2 ≤
        4*r^2+8*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1)+
          16*(T*a)*CF+16*T^2*c^2 := by
  sorry

end WeakHessian

end
end

end OAI
end
