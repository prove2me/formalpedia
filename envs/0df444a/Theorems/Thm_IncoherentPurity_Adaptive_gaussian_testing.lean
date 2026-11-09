-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_gaussian_testing
-- name    : IncoherentPurity.Adaptive.gaussian_testing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:06.371345+00:00
-- url     : https://prove2.me/theorems/cbd04c48-1647-4277-8be5-39c3b12549fa
-- title:
--   Theorem 6.7 — Adaptive Gaussian testing bound
-- statement:
--   Run the same parameter-independent adaptive query policy under the priors $N(0,v_iI_D)$, $i=0,1$, with $n$ queries of norm at most $L\ge0$. For all nonnegative variances, including zero, their seeded transcript laws satisfy
--
--   $$d_{\rm TV}(Q_{v_0},Q_{v_1})\le L\sqrt n\,|\sqrt{v_1}-\sqrt{v_0}|.$$
--
--   The policy has no access to the hypothesis or variance. The zero-variance endpoint uses the continuous extension of the positive-variance statement.
--
--   Differences from the source:
--   - generalization: the two positive variances v0, v1 of (6.5) → any two nonnegative variances v0, v1, including zero; reason: the proof (p.20) uses only s_i = √v_i and applies to every pair; (6.5) gives positive v0 < v1, which are instances
--   - encoding: TV distance and Gaussian transcript distributions → extended event supremum and integrated Gaussian likelihoods; reason: same probabilities, seed and adaptive history laws with no finiteness restriction
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Theorem 6.7, PDF p.20 = printed p.20

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Theorem 6.7, PDF p.20, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem gaussian_testing {D : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : QueryPolicy D Ω)
    (n : ℕ) (L v₀ v₁ : ℝ) (hL : IsBoundedQuery P L) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) :
  totalVariation (queryLaw P n v₀) (queryLaw P n v₁) ≤
    ENNReal.ofReal (L * Real.sqrt n * |Real.sqrt v₁ - Real.sqrt v₀|) := by sorry

end IncoherentPurity.Adaptive
