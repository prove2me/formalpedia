-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_test_comp_contDiff_bounded_laplacian
-- name    : OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:38:57.554255+00:00
-- url     : https://prove2.me/theorems/27b0caa4-916b-49fc-b4a3-80a8a9b68990
-- title:
--   OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian` of [lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/TestChain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/TestChain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`):
--
--   ```lean
--   lemma RCD.test_comp_contDiff_bounded_laplacian {K N : ℝ} (hN : 1 < N)
--       (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (o : X) {g : X → ℝ} (hg : IsTestFunction m g) {B : ℝ}
--       (hB : ∀ᵐ x ∂m,|laplacian m g x| ≤ B)
--       {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {C D E : ℝ≥0}
--       (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ))
--       (hE : LipschitzWith E (deriv (deriv φ))) (h0 : φ 0 = 0) :
--       IsTestFunction m (φ ∘ g) ∧ ∃ A : ℝ,∀ᵐ x ∂m,|laplacian m (φ ∘ g) x| ≤ A
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.IsTestFunction`, `OAI.WeakHessian.RCD` and `OAI.WeakHessian.laplacian` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/TestChain.lean (declaration OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian)

import Mathlib
import Definitions.Def_WeakHessian

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile121
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.test_comp_contDiff_bounded_laplacian {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g) {B : ℝ}
    (hB : ∀ᵐ x ∂m,|laplacian m g x| ≤ B)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {C D E : ℝ≥0}
    (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ))
    (hE : LipschitzWith E (deriv (deriv φ))) (h0 : φ 0 = 0) :
    IsTestFunction m (φ ∘ g) ∧ ∃ A : ℝ,∀ᵐ x ∂m,|laplacian m (φ ∘ g) x| ≤ A := by
  sorry
end WeakHessian

end
end InlinedFile121

end OAI
end
