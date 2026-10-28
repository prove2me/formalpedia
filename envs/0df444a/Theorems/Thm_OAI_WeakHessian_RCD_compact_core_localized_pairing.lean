-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_compact_core_localized_pairing
-- name    : OAI.WeakHessian.RCD.compact_core_localized_pairing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:41:59.397038+00:00
-- url     : https://prove2.me/theorems/8e797f89-a716-484b-b27d-16073fefdd1b
-- title:
--   OAI.WeakHessian.RCD.compact_core_localized_pairing: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.compact_core_localized_pairing` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreLocalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreLocalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma RCD.compact_core_localized_pairing {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
--       (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       (f : Lp ℝ 2 m)
--       (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
--         g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
--       {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
--       {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
--       {B : ℝ} (hB : ∀ x,|χ x| ≤ B) :
--       ∃ C : ℝ,0 ≤ C ∧ ∀ g,IsTestFunction m g → ∀ u A : Lp ℝ 2 m,
--         g =ᵐ[m] u → laplacian m g =ᵐ[m] A →
--         |⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ|
--           ≤ C*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.boundedMulLp` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.BoundedFunction`, `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.GloballyLipschitz`, `OAI.WeakHessian.InLaplacianDomain`, `OAI.WeakHessian.IsTestFunction`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev`, `OAI.WeakHessian.cheegerEnergy` and `OAI.WeakHessian.laplacian` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.RCD.compact_core_localized_sobolev` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreLocalization.lean (declaration OAI.WeakHessian.RCD.compact_core_localized_pairing)

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile159
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_localized_pairing {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ g,IsTestFunction m g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A →
      |⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ|
        ≤ C*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal)) := by
  sorry
end WeakHessian

end
end InlinedFile159

end OAI
end
