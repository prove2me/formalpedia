-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_prior_lower
-- name    : IncoherentPurity.Adaptive.prior_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:09.787829+00:00
-- url     : https://prove2.me/theorems/7235d126-a113-4bfa-aba6-5ab76e276a37
-- title:
--   Proposition 6.1 — Prior adaptive contributions
-- statement:
--   There are absolute $c,\varepsilon_0>0$ and $d_0>1$ such that for every integer $d\ge d_0$ and real $0<\varepsilon\le\varepsilon_0$, every successful adaptive incoherent protocol using $N$ copies satisfies
--
--   $$N\ge c\max\{d^{3/2}/\varepsilon,\sqrt d/\varepsilon^2\}.$$
--
--   The same protocol must succeed on all states, with the relative error and probability of Definition 1.1. The lower bound permits arbitrary measurable outcome spaces and parameter-independent shared randomness.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Proposition 6.1, PDF p.17 = printed p.17

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Proposition 6.1, PDF p.17, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem prior_lower : ∃ (c ε₀ : ℝ) (d₀ : ℕ), 0 < c ∧ 0 < ε₀ ∧ 1 < d₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
  ∀ (N : ℕ) (P : Protocol d), Succeeds P N ε → c * (max ((d : ℝ)*Real.sqrt d/ε) (Real.sqrt d/ε^2)) ≤ (N : ℝ) := by sorry

end IncoherentPurity.Adaptive
