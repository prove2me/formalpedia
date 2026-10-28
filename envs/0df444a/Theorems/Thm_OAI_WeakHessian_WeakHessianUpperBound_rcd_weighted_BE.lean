-- Prove2me | Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_rcd_weighted_BE
-- name    : OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:42:50.694342+00:00
-- url     : https://prove2.me/theorems/033c3281-d98d-46f9-b561-d0dfd0be9383
-- title:
--   OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE` of [lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/WeightedBE.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/WeightedBE.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma WeakHessianUpperBound.rcd_weighted_BE {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (o : X) {F G u A ξ B : X → ℝ} (hHess : WeakHessianUpperBound m F G)
--       {L : ℝ≥0} (hF : LipschitzWith L F)
--       {CF Cξ CG CB : ℝ} (hFbounded : ∀ x,|F x| ≤ CF)
--       (hGbounded : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
--       (hu : IsLaplacian (exponentialMeasure m (fun x => a*F x)) u A)
--       (hAS : Sobolev (exponentialMeasure m (fun x => a*F x)) A)
--       (hξA : IsLaplacian (exponentialMeasure m (fun x => a*F x)) ξ B)
--       (hξbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
--       (hBbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|B x| ≤ CB)
--       (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x) :
--       (∫ x,(ξ x*(K-a*G x))*gamma (exponentialMeasure m (fun x => a*F x)) u u x
--         ∂exponentialMeasure m (fun x => a*F x)) ≤
--         (1/2)*(∫ x,B x*gamma (exponentialMeasure m (fun x => a*F x)) u u x
--           ∂exponentialMeasure m (fun x => a*F x))-
--         ∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) u A x
--           ∂exponentialMeasure m (fun x => a*F x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.exponentialMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.IsLaplacian`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev`, `OAI.WeakHessian.WeakHessianUpperBound` and `OAI.WeakHessian.gamma` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proofs of `OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds`, `OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound` and `OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient` of this split import it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/WeightedBE.lean (declaration OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile180
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_BE {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G u A ξ B : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F)
    {CF Cξ CG CB : ℝ} (hFbounded : ∀ x,|F x| ≤ CF)
    (hGbounded : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (hu : IsLaplacian (exponentialMeasure m (fun x => a*F x)) u A)
    (hAS : Sobolev (exponentialMeasure m (fun x => a*F x)) A)
    (hξA : IsLaplacian (exponentialMeasure m (fun x => a*F x)) ξ B)
    (hξbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hBbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|B x| ≤ CB)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x) :
    (∫ x,(ξ x*(K-a*G x))*gamma (exponentialMeasure m (fun x => a*F x)) u u x
      ∂exponentialMeasure m (fun x => a*F x)) ≤
      (1/2)*(∫ x,B x*gamma (exponentialMeasure m (fun x => a*F x)) u u x
        ∂exponentialMeasure m (fun x => a*F x))-
      ∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) u A x
        ∂exponentialMeasure m (fun x => a*F x) := by
  sorry
end WeakHessian

end
end InlinedFile180

end OAI
end
