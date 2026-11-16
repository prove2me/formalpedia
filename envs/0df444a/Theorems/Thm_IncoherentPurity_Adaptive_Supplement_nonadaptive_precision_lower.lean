-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_Supplement_nonadaptive_precision_lower
-- name    : IncoherentPurity.Adaptive.Supplement.nonadaptive_precision_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:33.58814+00:00
-- url     : https://prove2.me/theorems/73a1fe47-c2b9-4c71-8b5f-6c068b6824f6
-- title:
--   Non-adaptive precision contribution
-- statement:
--   There is an absolute $\varepsilon_0>0$, which can be chosen at most $1/576$, such that for every integer $d\ge16$ and $0<\varepsilon\le\varepsilon_0$, every non-adaptive incoherent protocol that estimates the purity of every $d$-dimensional state to relative error $\varepsilon$ with success probability at least $2/3$ needs
--
--   $$N\ge\frac{d}{576\varepsilon^2}.$$
--
--   The bound covers arbitrary measurable single-copy POVMs and shared classical randomness in the published protocol model. It supplies the precision term of Theorem 5.1. The coefficient $1/576$ is the explicit witness established by Equation (5.17), rather than a claim about the optimal leading constant.
--
--   Differences from the source:
--   - encoding: Omega(d/epsilon squared) with a universal sufficiently small precision threshold → the proof witness N at least d/(576 epsilon squared), with an existential universal threshold at most 1/576; reason: Equation (5.17) gives this coefficient, and the Section 5 common threshold is chosen no larger than 1/576; no precision instance below the existential threshold is removed
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), preprint, pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce; Proposition 5.4, PDF p.17 = printed p.17; Eq. (5.17) for the explicit proof witness

import Definitions.Def_IncoherentPurity_Adaptive_Supplement_Testing

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive.Supplement

/-- Proposition 5.4, PDF = printed p.17; pinned source SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem nonadaptive_precision_lower : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1/576 ∧
  ∀ d : ℕ, 16 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
  ∀ (N : ℕ) (P : Protocol d), IsNonadaptive P → Succeeds P N ε →
    (d : ℝ)/(576*ε^2) ≤ (N : ℝ) := by sorry

end IncoherentPurity.Adaptive.Supplement
