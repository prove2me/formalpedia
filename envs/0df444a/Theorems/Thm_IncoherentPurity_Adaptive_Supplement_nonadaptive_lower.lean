-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_Supplement_nonadaptive_lower
-- name    : IncoherentPurity.Adaptive.Supplement.nonadaptive_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:05.584971+00:00
-- url     : https://prove2.me/theorems/c39315fc-c64a-453b-905c-05e7a9bf89d9
-- title:
--   Non-adaptive purity estimation: full lower bound
-- statement:
--   There exist absolute constants $c,\varepsilon_0>0$ and an integer $d_0>1$ such that for every $d\ge d_0$ and every $0<\varepsilon\le\varepsilon_0$, every non-adaptive incoherent protocol that estimates the purity of every $d$-dimensional state to relative error $\varepsilon$ with probability at least $2/3$ satisfies
--
--   $$N\ge c\max\!\left\{\frac{d^{3/2}}{\varepsilon},\frac d{\varepsilon^2}\right\}.$$
--
--   The protocol may use arbitrary measurable single-copy POVM outcomes and shared classical randomness. The constants are uniform jointly in dimension and precision and precede the budget and protocol quantifiers. This companion theorem collects both lower-bound contributions; the published mixedness result supplies one contribution and Proposition 5.4 supplies the other.
--
--   Differences from the source:
--   - encoding: Omega of the maximum rate for all sufficiently large dimensions and all sufficiently small positive precisions → a universal positive constant and dimension/precision thresholds, followed by every non-adaptive successful protocol; reason: this is the operational uniform lower-bound meaning of the source claim
--   - encoding: d to the power three halves → (d : real) times sqrt d; reason: these agree for every positive dimension
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), preprint, pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce; Theorem 5.1, PDF p.15 = printed p.15

import Definitions.Def_IncoherentPurity_Adaptive_Supplement_Spike

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive.Supplement

/-- Theorem 5.1, PDF = printed p.15; pinned source SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem nonadaptive_lower : ∃ (c ε₀ : ℝ) (d₀ : ℕ),
  0 < c ∧ 0 < ε₀ ∧ 1 < d₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
  ∀ (N : ℕ) (P : Protocol d), IsNonadaptive P → Succeeds P N ε →
    c * max ((d : ℝ)*Real.sqrt d/ε) ((d : ℝ)/ε^2) ≤ (N : ℝ) := by sorry

end IncoherentPurity.Adaptive.Supplement
