-- Prove2me | Theorems.Thm_OAI_WeakHessian_RCD_compact_core_product_identity
-- name    : OAI.WeakHessian.RCD.compact_core_product_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:53:52.448349+00:00
-- url     : https://prove2.me/theorems/5bdba68d-629d-48ba-9620-4adaac92ec58
-- title:
--   OAI.WeakHessian.RCD.compact_core_product_identity: intermediate lemma from OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakHessian.RCD.compact_core_product_identity` of [lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakHessian`, with `open Set Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`, `open Set Filter MeasureTheory WeakHessianFunctional`, `open scoped Topology ENNReal NNReal InnerProductSpace`):
--
--   ```lean
--   lemma RCD.compact_core_product_identity {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
--       (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
--       (f : Lp ℝ 2 m)
--       (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
--         g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
--       {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
--       {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
--       {B : ℝ} (hB : ∀ x,|χ x| ≤ B)
--       (g : X → ℝ) (hg : IsTestFunction m g) (u A : Lp ℝ 2 m)
--       (hgu : g =ᵐ[m] u) (hgA : laplacian m g =ᵐ[m] A) :
--       ⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ =
--         ⟪f,boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) u -
--           boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD u -
--           (2:ℝ) • (memLp_gamma_of_lipschitz hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
--             hχ.2.2.1.choose_spec (laplacian_isLaplacian hg.1).1).toLp (gamma m χ g)⟫_ℝ
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakHessian.boundedMulLp` (definitions bundle `OAIQ52Wh001` of this split); `OAI.WeakHessian.laplacian_isLaplacian` (definitions bundle `OAIQ52Wh004` of this split); `OAI.WeakHessian.CurvatureDimension.global_localGradientParallelogram` (definitions bundle `OAIQ52Wh005` of this split); `OAI.WeakHessian.memLp_gamma_of_lipschitz` (definitions bundle `OAIQ52Wh007` of this split); `OAI.WeakHessian.BoundedFunction`, `OAI.WeakHessian.CurvatureDimension`, `OAI.WeakHessian.FiniteOnBoundedSets`, `OAI.WeakHessian.FullSupport`, `OAI.WeakHessian.GloballyLipschitz`, `OAI.WeakHessian.InLaplacianDomain`, `OAI.WeakHessian.IsTestFunction`, `OAI.WeakHessian.QuadraticCheegerEnergy`, `OAI.WeakHessian.RCD`, `OAI.WeakHessian.Sobolev`, `OAI.WeakHessian.gamma` and `OAI.WeakHessian.laplacian` (the published bundle `Def_WeakHessian`).
--
--   **Used by.** The proof of `OAI.WeakHessian.RCD.compact_core_weak_equation` of this split imports it.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactCoreIdentity.lean (declaration OAI.WeakHessian.RCD.compact_core_product_identity)

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

section InlinedFile161
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_product_identity {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B)
    (g : X → ℝ) (hg : IsTestFunction m g) (u A : Lp ℝ 2 m)
    (hgu : g =ᵐ[m] u) (hgA : laplacian m g =ᵐ[m] A) :
    ⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ =
      ⟪f,boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) u -
        boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD u -
        (2:ℝ) • (memLp_gamma_of_lipschitz hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
          hχ.2.2.1.choose_spec (laplacian_isLaplacian hg.1).1).toLp (gamma m χ g)⟫_ℝ := by
  sorry
end WeakHessian

end
end InlinedFile161

end OAI
end
