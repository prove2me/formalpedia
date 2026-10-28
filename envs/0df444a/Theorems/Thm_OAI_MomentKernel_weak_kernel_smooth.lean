-- Prove2me | Theorems.Thm_OAI_MomentKernel_weak_kernel_smooth
-- name    : OAI.MomentKernel.weak_kernel_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T05:15:25.285921+00:00
-- url     : https://prove2.me/theorems/f1c4875a-71dc-4f0a-9bc6-489eec90e23c
-- title:
--   OAI.MomentKernel.weak_kernel_smooth: intermediate lemma from OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MomentKernel.weak_kernel_smooth` of [lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MomentKernel`, with `open scoped Real`, `open MeasureTheory`, `open scoped Topology`, `open MeasureTheory FourierTransform Convolution`, `open scoped SchwartzMap`, `open MeasureTheory FourierTransform TemperedDistribution`, `open scoped SchwartzMap Topology`, `open MeasureTheory TemperedDistribution FourierTransform LineDeriv`, `open scoped SchwartzMap ContDiff`, `open Filter Function`, `open scoped SchwartzMap Topology ContDiff`, `open MeasureTheory FourierTransform TemperedDistribution`, `open scoped SchwartzMap Topology ContDiff`, `open MeasureTheory`, `open scoped Topology ContDiff`, `open Matrix`, `open scoped ContDiff Matrix.Norms.Elementwise`, `open scoped ContDiff Topology`, `open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates`, `open scoped ContDiff`):
--
--   ```lean
--   theorem weak_kernel_smooth {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
--       (hV : ContDiff ℝ ∞ V) (hpos : ∀ z, (hess φ z).PosDef) {Z m : ℝ} (hZ : 0 < Z)
--       (hVlower : ∀ x, m ≤ V x)
--       (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
--       {g : Space ι → ℝ} (hg : MemLp g 2 (targetMeasure volume V Z))
--       (hweak : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
--         (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
--           (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure volume V Z) = 0) :
--       ∃ w : Space ι → ℝ, ContDiff ℝ ∞ w ∧ g =ᵐ[targetMeasure volume V Z] w
--   ```
--
--   **Definitions.** The statement is written with `OAI.DensityEnergy.A`, `OAI.DensityEnergy.Space`, `OAI.MomentCoordinates.Space`, `OAI.MomentCoordinates.hess`, `OAI.MomentOperator.tau` and `OAI.TargetCoordinates.targetMeasure` (definitions bundle `OAIW2LB000` of this split).
--
--   **Used by.** The proof of `OAI.MomentSlab.variance_from_moment` of this split imports it.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (declaration OAI.MomentKernel.weak_kernel_smooth)

import Mathlib
import Definitions.Def_OAIW2LB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Real

open MeasureTheory
open scoped Topology

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff

open Filter Function
open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff

open MeasureTheory
open scoped Topology ContDiff

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

open scoped ContDiff Topology

noncomputable section

namespace MomentKernel

open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weak_kernel_smooth {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ z, (hess φ z).PosDef) {Z m : ℝ} (hZ : 0 < Z)
    (hVlower : ∀ x, m ≤ V x)
    (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {g : Space ι → ℝ} (hg : MemLp g 2 (targetMeasure volume V Z))
    (hweak : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
        (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure volume V Z) = 0) :
    ∃ w : Space ι → ℝ, ContDiff ℝ ∞ w ∧ g =ᵐ[targetMeasure volume V Z] w := by
  sorry

end MomentKernel

end

open Matrix
open scoped BigOperators Kronecker

open MeasureTheory
open scoped BigOperators

open scoped BigOperators InnerProductSpace Topology

end

end OAI
end
