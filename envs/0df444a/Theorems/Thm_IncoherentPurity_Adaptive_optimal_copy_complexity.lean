-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_optimal_copy_complexity
-- name    : IncoherentPurity.Adaptive.optimal_copy_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:02.321607+00:00
-- url     : https://prove2.me/theorems/dfb97a4d-4214-45db-b085-c86f8a988047
-- title:
--   Theorem 1.3 — Tight adaptive relative-error purity copy complexity
-- statement:
--   There are absolute constants $c,C,\varepsilon_0>0$ and an integer $d_0>1$ such that for every integer $d\ge d_0$ and real $0<\varepsilon\le\varepsilon_0$, let
--
--   $$F(d,\varepsilon)=\min\{d/\varepsilon^2+d^{3/2}/\varepsilon,\ d^2/\varepsilon+\sqrt d/\varepsilon^2\}.$$
--
--   Some adaptive incoherent protocol succeeds for all $d$-dimensional states using at most $CF(d,\varepsilon)$ copies. Every successful such protocol with fixed budget $N$ has $N\ge cF(d,\varepsilon)$. Success has relative error $\varepsilon$ and probability at least $2/3$. POVMs have arbitrary measurable outcomes, and classical randomization and adaptation are unrestricted. The constants precede dimension, precision, budgets, protocols and states, so both bounds hold jointly uniformly.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Theorem 1.3, PDF p.4 = printed p.4

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Theorem 1.3, PDF p.4, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem optimal_copy_complexity : ∃ (c C ε₀ : ℝ) (d₀ : ℕ),
  0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ 1 < d₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    (∃ (N : ℕ) (P : Protocol d), Succeeds P N ε ∧ (N : ℝ) ≤ C * rate d ε) ∧
    (∀ (N : ℕ) (P : Protocol d), Succeeds P N ε → c * rate d ε ≤ (N : ℝ)) := by sorry

end IncoherentPurity.Adaptive
