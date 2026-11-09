-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_transcript_score
-- name    : IncoherentPurity.Adaptive.transcript_score
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:22.421202+00:00
-- url     : https://prove2.me/theorems/167295f6-3f9c-40fe-a51e-a10ed65ace62
-- title:
--   Lemma 6.10 — Adaptive Gaussian transcript score
-- statement:
--   For a parameter-independent adaptive query policy, let $T_j$ be its first $0\le j\le n$ responses and seed under the prior $N(0,s^2I_D)$, with $s>0$. Write $q_{s,j}$ for its actual transcript density and $m_j,C_j$ for its Bayesian posterior mean and covariance. Almost surely the logarithmic density is differentiable and
--
--   $$\partial_s\log q_{s,j}(T_j)=\frac{\|m_j\|_2^2+\operatorname{tr}C_j}{s^3}-\frac D s.$$
--
--   The policy is fixed as $s$ varies; neither the prior scale nor the vector is an input to it.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 6.10, PDF p.21 = printed p.21

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 6.10, PDF p.21, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem transcript_score {D : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : QueryPolicy D Ω) (n j : ℕ)
    (hj : j ≤ n) (s : ℝ) (hs : 0 < s) :
  ∀ᵐ h ∂queryLaw P j (s^2),
    DifferentiableAt ℝ (fun t => Real.log (queryDensity P j (t^2) h)) s ∧
    queryScore P j s h =
      (normSq (posteriorMean P j s h) + (posteriorCov P j s h).trace) / s^3 - (D : ℝ)/s := by sorry

end IncoherentPurity.Adaptive
