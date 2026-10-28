-- Prove2me | Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_rcd_core_integrated
-- name    : OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:39:54.82361+00:00
-- url     : https://prove2.me/theorems/f87f0ed4-6651-46c9-a575-f242a9510a70
-- title:
--   OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated` of [lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/ActualCore.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/ActualCore.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma WeakHessianUpperBound.rcd_core_integrated {K N : ℝ}
--       (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (o : X) {F G g ξ : X → ℝ} (hHess : WeakHessianUpperBound m F G)
--       (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
--       {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
--       {B C D : ℝ} (hB : ∀ x,|F x| ≤ B) (hC : ∀ x,|ξ x| ≤ C)
--       (hG : ∀ x,|G x| ≤ D) (hGc : Continuous G)
--       (hξc : HasCompactSupport ξ) (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a) :
--       (∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
--         driftBochner m (fun x => a*F x) g ξ
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.driftBochner` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.IsTestFunction`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.WeakHessianUpperBound` and `OAI.WeakHessian.gamma` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/ActualCore.lean (declaration OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated)

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

section InlinedFile112
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_core_integrated {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G g ξ : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x,|F x| ≤ B) (hC : ∀ x,|ξ x| ≤ C)
    (hG : ∀ x,|G x| ≤ D) (hGc : Continuous G)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  sorry
end WeakHessian

end
end InlinedFile112

end OAI
end
