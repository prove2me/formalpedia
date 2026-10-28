-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_gamma_memLp
-- name    : OAI.WeakHessian.RCD.weighted_heat_gamma_memLp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:53:46.071681+00:00
-- url     : https://prove2.me/theorems/70b97aba-f9cd-464f-83f9-67c1625b3924
-- title:
--   OAI.WeakHessian.RCD.weighted_heat_gamma_memLp: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.weighted_heat_gamma_memLp` of [lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatGammaL2.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatGammaL2.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma RCD.weighted_heat_gamma_memLp {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
--       (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
--       (h : QuadraticCheegerEnergy (exponentialMeasure m V))
--       {u A : Lp ℝ 2 (exponentialMeasure m V)}
--       (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
--       {Bu BA : ℝ} (hBu : 0 ≤ Bu) (hBA : 0 ≤ BA)
--       (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ Bu)
--       (hAb : ∀ᵐ x ∂exponentialMeasure m V,|A x| ≤ BA) {t : ℝ} (ht : 0 ≤ t) :
--       MemLp (gamma (exponentialMeasure m V) (cheegerHeat h t u) (cheegerHeat h t u)) 2
--         (exponentialMeasure m V)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.exponentialMeasure` (definitions bundle `OAIQ52Wh002` of this split); `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.IsFormGenerator` (definitions bundle `OAIQ52Wh004` of this split); `OAI.WeakHessian.cheegerHeat` and `OAI.WeakHessian.cheeger_closedQuadraticEnergy` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.cheegerEnergy` and `OAI.WeakHessian.gamma` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proofs of `OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds`, `OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound` and `OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient` of this split import it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/HeatFlow/WeightedHeatGammaL2.lean (declaration OAI.WeakHessian.RCD.weighted_heat_gamma_memLp)

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

section InlinedFile200
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_gamma_memLp {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {u A : Lp ℝ 2 (exponentialMeasure m V)}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {Bu BA : ℝ} (hBu : 0 ≤ Bu) (hBA : 0 ≤ BA)
    (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ Bu)
    (hAb : ∀ᵐ x ∂exponentialMeasure m V,|A x| ≤ BA) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (gamma (exponentialMeasure m V) (cheegerHeat h t u) (cheegerHeat h t u)) 2
      (exponentialMeasure m V) := by
  sorry
end WeakHessian

end
end InlinedFile200

end OAI
end
