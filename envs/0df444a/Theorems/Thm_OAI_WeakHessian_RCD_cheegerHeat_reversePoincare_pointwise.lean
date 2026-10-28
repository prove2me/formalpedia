-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_reversePoincare_pointwise
-- name    : OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:51:05.389007+00:00
-- url     : https://prove2.me/theorems/84841aca-84e6-4277-8c72-1682db97df05
-- title:
--   OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise` of [lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/ReversePoincarePointwise.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/ReversePoincarePointwise.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma RCD.cheegerHeat_reversePoincare_pointwise {K N : ℝ} (hN : 1 < N)
--       (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
--       (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
--       (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
--       {t : ℝ} (ht : 0 < t) :
--       ∀ᵐ x ∂m,2*t*Real.exp (-2*|K| *t)*(weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2 ≤ (n:ℝ)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.cheegerHeat` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD` and `OAI.WeakHessian.weakGradient` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proofs of `OAI.WeakHessian.RCD.compact_core_localized_sobolev`, `OAI.WeakHessian.RCD.compact_core_weak_equation`, `OAI.WeakHessian.RCD.weighted_heat_boundedLipschitzRepresentative`, `OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn`, `OAI.WeakHessian.RCD.weighted_heat_gamma_memLp` and `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE` of this split import it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/LocalBounds/ReversePoincarePointwise.lean (declaration OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise)

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

section InlinedFile139
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_reversePoincare_pointwise {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂m,2*t*Real.exp (-2*|K| *t)*(weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2 ≤ (n:ℝ)^2 := by
  sorry

end WeakHessian

end
end InlinedFile139

end OAI
end
