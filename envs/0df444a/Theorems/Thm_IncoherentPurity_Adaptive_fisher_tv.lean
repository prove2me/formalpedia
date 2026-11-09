-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_fisher_tv
-- name    : IncoherentPurity.Adaptive.fisher_tv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:29.58213+00:00
-- url     : https://prove2.me/theorems/e5b39866-314e-4a9e-b818-9722bf8e78e1
-- title:
--   Fact 2.3 — Total variation controlled by Fisher information
-- statement:
--   Let $p_s$ be a differentiable family of normalized densities against a common dominating measure, absolutely continuous in the parameter for almost every outcome as in Definition 2.2. Suppose its Fisher information $I_s$ is finite between parameters $a,b$. Then
--
--   $$d_{\rm TV}(p_a,p_b)\le\frac12\left|\int_a^b\sqrt{I_s}\,ds\right|.$$
--
--   The right side is represented by a nonnegative extended integral over the unordered interval. It equals the displayed absolute integral when finite and remains $+\infty$ if it diverges, rather than defaulting to zero.
--
--   Differences from the source:
--   - encoding: absolute integral of the square root of Fisher information → extended nonnegative integral over the unordered endpoint interval; reason: retains the finite value and represents divergence by infinity; common densities and their parameter absolute continuity remain explicit
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Fact 2.3, PDF p.9 = printed p.9

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Fact 2.3, PDF p.9, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem fisher_tv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a b : ℝ)
    (F : DensityFamily Ω μ a b) (hI : ∀ s ∈ Set.uIcc a b, densityFisher F s < ⊤) :
  totalVariation (densityLaw F a) (densityLaw F b) ≤
    (1/2 : ℝ≥0∞) * ∫⁻ s in Set.uIcc a b, (densityFisher F s) ^ (1/2 : ℝ) := by sorry

end IncoherentPurity.Adaptive
