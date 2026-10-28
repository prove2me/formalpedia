-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_compact_core_localized_sobolev
-- name    : OAI.WeakHessian.RCD.compact_core_localized_sobolev
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:38:03.22071+00:00
-- url     : https://prove2.me/theorems/cfe5ea46-af14-4082-85e6-c9b2370faf7a
-- title:
--   OAI.WeakHessian.RCD.compact_core_localized_sobolev: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.compact_core_localized_sobolev` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma RCD.compact_core_localized_sobolev {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
--       (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       (f : Lp ℝ 2 m)
--       (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
--         g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
--       {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
--       {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D) :
--       Sobolev m (fun x => f x*χ x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.IsTestFunction`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev` and `OAI.WeakHessian.laplacian` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proofs of `OAI.WeakHessian.RCD.compact_core_weak_equation` and `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality` of this split import it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreRegularity.lean (declaration OAI.WeakHessian.RCD.compact_core_localized_sobolev)

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

section InlinedFile160
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_localized_sobolev {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D) :
    Sobolev m (fun x => f x*χ x) := by
  sorry
end WeakHessian

end
end InlinedFile160

end OAI
end
