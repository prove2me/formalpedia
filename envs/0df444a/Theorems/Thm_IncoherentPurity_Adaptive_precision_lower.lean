-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_precision_lower
-- name    : IncoherentPurity.Adaptive.precision_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:41.241795+00:00
-- url     : https://prove2.me/theorems/1ba3e8e0-c536-40d1-939b-20d6ac7d0b62
-- title:
--   Theorem 6.2 — Adaptive precision lower bound
-- statement:
--   There are absolute $c,\varepsilon_0>0$ and integer $d_0>1$ such that every $d\ge d_0$, $0<\varepsilon\le\varepsilon_0$, and successful adaptive incoherent protocol with budget $N$ satisfy
--
--   $$N\ge c\min\{d/\varepsilon^2,d^2/\varepsilon\}.$$
--
--   The protocol must succeed for every state and may use arbitrary measurable POVM outcomes and shared classical randomness.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Theorem 6.2, PDF p.18 = printed p.18

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Theorem 6.2, PDF p.18, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem precision_lower : ∃ (c ε₀ : ℝ) (d₀ : ℕ), 0 < c ∧ 0 < ε₀ ∧ 1 < d₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
  ∀ (N : ℕ) (P : Protocol d), Succeeds P N ε →
    c * min ((d : ℝ)/ε^2) ((d : ℝ)^2/ε) ≤ (N : ℝ) := by sorry

end IncoherentPurity.Adaptive
