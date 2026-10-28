-- Prove2me | Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_heatBridge_bounds
-- name    : OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:54:18.020098+00:00
-- url     : https://prove2.me/theorems/a7e24b98-0568-4b1c-9431-ff870dd31d09
-- title:
--   OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Sobolev/LocalizedGradient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Sobolev/LocalizedGradient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma WeakHessianUpperBound.heatBridge_bounds {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
--       {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
--       (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
--       (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
--       {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
--       (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
--       {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
--       (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
--       (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
--       {T s : ℝ} (hs : s ∈ Icc 0 T) :
--       heatBridgeEnergy h f ξ T 0 ≤ Real.exp (2*(|K|+a*CG)*T)*heatBridgeEnergy h f ξ T s ∧
--       heatBridgeEnergy h f ξ T s ≤ Real.exp (2*(|K|+a*CG)*T)*heatBridgeEnergy h f ξ T T
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.exponentialMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.heatBridgeEnergy` (definitions bundle `OAIQ52Wh007` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev` and `OAI.WeakHessian.WeakHessianUpperBound` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proofs of `OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient` and `OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law` of this split import it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Sobolev/LocalizedGradient.lean (declaration OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007

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
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.heatBridge_bounds {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeEnergy h f ξ T 0 ≤ Real.exp (2*(|K|+a*CG)*T)*heatBridgeEnergy h f ξ T s ∧
    heatBridgeEnergy h f ξ T s ≤ Real.exp (2*(|K|+a*CG)*T)*heatBridgeEnergy h f ξ T T := by
  sorry

end WeakHessian

end
end

end OAI
end
