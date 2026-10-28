-- Prove2me | Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_localized_heatError_tail_bound
-- name    : OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:54:45.02699+00:00
-- url     : https://prove2.me/theorems/5137caf9-567c-469b-9562-e3e31c629fb2
-- title:
--   OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Measure/CurvatureTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Measure/CurvatureTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma WeakHessianUpperBound.localized_heatError_tail_bound {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
--       {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
--       (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
--       (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
--       {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
--       (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
--       {Lf : ℝ} (hLf : 0 ≤ Lf)
--       (hDb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|weakGradient (exponentialMeasure m (fun x => a*F x)) f x| ≤ Lf)
--       (hξi : Integrable ξ (exponentialMeasure m (fun x => a*F x)))
--       {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
--       (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
--       (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
--       {d β r R T U Q c : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
--       (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 (exponentialMeasure m (fun x => a*F x)))
--       (hsupp : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),r ≤ dist x o → ξ x = 0)
--       (hlocal : ∀ x,dist x o < R → G x ≤ c)
--       (hT : 0 ≤ T) (hTU : T ≤ U)
--       (hQ : ‖ξ‖*‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖ ≤ Q) :
--       localizedHeatError h ξ G K a c CG T f ≤ curvatureTailBound K a c CG U Lf Q d β R r
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.curvatureTailBound` and `OAI.WeakHessian.exponentialMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.localizedHeatError` (definitions bundle `OAIQ52Wh007` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev`, `OAI.WeakHessian.WeakHessianUpperBound` and `OAI.WeakHessian.weakGradient` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Measure/CurvatureTail.lean (declaration OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound)

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
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.localized_heatError_tail_bound {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Lf : ℝ} (hLf : 0 ≤ Lf)
    (hDb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|weakGradient (exponentialMeasure m (fun x => a*F x)) f x| ≤ Lf)
    (hξi : Integrable ξ (exponentialMeasure m (fun x => a*F x)))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {d β r R T U Q c : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 (exponentialMeasure m (fun x => a*F x)))
    (hsupp : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),r ≤ dist x o → ξ x = 0)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T ≤ U)
    (hQ : ‖ξ‖*‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖ ≤ Q) :
    localizedHeatError h ξ G K a c CG T f ≤ curvatureTailBound K a c CG U Lf Q d β R r := by
  sorry

end WeakHessian

end
end

end OAI
end
