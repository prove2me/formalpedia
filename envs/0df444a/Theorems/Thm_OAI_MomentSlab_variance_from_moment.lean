-- Prove2me | Theorems.Thm_OAI_MomentSlab_variance_from_moment
-- name    : OAI.MomentSlab.variance_from_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T05:15:10.315372+00:00
-- url     : https://prove2.me/theorems/20bfde07-03b7-4e38-8c14-72fac4fe74a7
-- title:
--   OAI.MomentSlab.variance_from_moment: intermediate lemma from OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MomentSlab.variance_from_moment` of [lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MomentSlab`, with `open scoped Real`, `open MeasureTheory`, `open scoped Topology`, `open MeasureTheory FourierTransform Convolution`, `open scoped SchwartzMap`, `open MeasureTheory FourierTransform TemperedDistribution`, `open scoped SchwartzMap Topology`, `open MeasureTheory TemperedDistribution FourierTransform LineDeriv`, `open scoped SchwartzMap ContDiff`, `open Filter Function`, `open scoped SchwartzMap Topology ContDiff`, `open MeasureTheory FourierTransform TemperedDistribution`, `open scoped SchwartzMap Topology ContDiff`, `open MeasureTheory`, `open scoped Topology ContDiff`, `open Matrix`, `open scoped ContDiff Matrix.Norms.Elementwise`, `open scoped ContDiff Topology`, `open Matrix`, `open scoped BigOperators Kronecker`, `open MeasureTheory`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace Topology`, `open MeasureTheory WeightedCalculus MomentCoordinates TargetCoordinates SoftSlab FullTensor`, `open scoped ContDiff`):
--
--   ```lean
--   theorem variance_from_moment {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
--       (p : κ → ι → ℝ) (h : κ → ℝ) (hp : ∀ i, p i ≠ 0) (hh : ∀ i, 0 < h i)
--       {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ z, (hess φ z).PosDef)
--       (hupper : ∀ z, ((4/ε) • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
--       (heq : ∀ z, Real.log (hess φ z).det = potential ε p h (q+2) (grad φ z)+
--         Real.log (∫ x, Real.exp (-potential ε p h (q+2) x))-φ z)
--       (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
--       (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
--       (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = law ε p h (q+2)) (b : κ → ℝ) :
--       (∫ x, (∑ i, b i*summand (p i) (h i) (q+2) x)^2 ∂law ε p h (q+2))-
--         (∫ x, ∑ i, b i*summand (p i) (h i) (q+2) x ∂law ε p h (q+2))^2 ≤
--         ∑ i, b i^2*(∫ x, summand (p i) (h i) (q+2) x ∂law ε p h (q+2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MomentCoordinates.Space`, `OAI.MomentCoordinates.grad`, `OAI.MomentCoordinates.hess`, `OAI.SoftSlab.law`, `OAI.SoftSlab.potential`, `OAI.SoftSlab.summand` and `OAI.TargetCoordinates.sourceMeasure` (definitions bundle `OAIW2LB000` of this split).
--
--   **Used by.** The proof of `OAI.LogBrunnMinkowski.softVariance` of this split imports it.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (declaration OAI.MomentSlab.variance_from_moment)

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

open Matrix
open scoped BigOperators Kronecker

open MeasureTheory
open scoped BigOperators

open scoped BigOperators InnerProductSpace Topology

noncomputable section

namespace MomentSlab
open MeasureTheory WeightedCalculus MomentCoordinates TargetCoordinates SoftSlab FullTensor
open scoped ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem variance_from_moment {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (hp : ∀ i, p i ≠ 0) (hh : ∀ i, 0 < h i)
    {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ z, (hess φ z).PosDef)
    (hupper : ∀ z, ((4/ε) • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = potential ε p h (q+2) (grad φ z)+
      Real.log (∫ x, Real.exp (-potential ε p h (q+2) x))-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = law ε p h (q+2)) (b : κ → ℝ) :
    (∫ x, (∑ i, b i*summand (p i) (h i) (q+2) x)^2 ∂law ε p h (q+2))-
      (∫ x, ∑ i, b i*summand (p i) (h i) (q+2) x ∂law ε p h (q+2))^2 ≤
      ∑ i, b i^2*(∫ x, summand (p i) (h i) (q+2) x ∂law ε p h (q+2)) := by
  sorry

end MomentSlab
end

end

end OAI
end
