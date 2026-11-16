-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_Supplement_nonadaptive_copy_complexity
-- name    : IncoherentPurity.Adaptive.Supplement.nonadaptive_copy_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:20.409201+00:00
-- url     : https://prove2.me/theorems/2161ac4e-2775-4ed7-b188-b351c53cdc70
-- title:
--   Non-adaptive purity estimation: tight copy complexity
-- statement:
--   A non-adaptive incoherent protocol measures each fresh copy separately, chooses its entire POVM schedule before seeing outcomes, and may use shared classical randomness. It succeeds if, for every $d$-dimensional state $\rho$, its estimate obeys $|\widehat P-\operatorname{tr}(\rho^2)|\le\varepsilon\operatorname{tr}(\rho^2)$ with probability at least $2/3$.
--
--   There exist absolute constants $c,C,\varepsilon_0>0$ and an integer $d_0>1$ such that, for every $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$, writing $B(d,\varepsilon)=\max\{d/\varepsilon^2,d^{3/2}/\varepsilon\}$,
--
--   $$\begin{aligned}&\text{some successful non-adaptive protocol uses }N\le C B(d,\varepsilon),\\&\text{every successful non-adaptive protocol uses }N\ge c B(d,\varepsilon).\end{aligned}$$
--
--   Both statements allow arbitrary measurable POVM outcomes and the published shared-seed protocol model. The constants and thresholds are chosen before dimension, precision, budget or protocol. This companion theorem supplies the full non-adaptive characterization alongside the adaptive goal.
--
--   Differences from the source:
--   - encoding: Theta of the maximum rate → uniform positive constants and thresholds with operational existence and universal lower clauses; reason: this spells out both sides of the source asymptotic claim without changing any regime
--   - encoding: d to the power three halves → (d : real) times sqrt d; reason: these agree for every positive dimension
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), preprint, pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce; Theorem 1.2, PDF p.4 = printed p.4

import Definitions.Def_IncoherentPurity_Adaptive_Supplement_Spike

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive.Supplement

/-- Theorem 1.2, PDF = printed p.4; pinned source SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem nonadaptive_copy_complexity : ∃ (c C ε₀ : ℝ) (d₀ : ℕ),
  0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ 1 < d₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    (∃ (N : ℕ) (P : Protocol d), IsNonadaptive P ∧ Succeeds P N ε ∧
      (N : ℝ) ≤ C * max ((d : ℝ)/ε^2) ((d : ℝ)*Real.sqrt d/ε)) ∧
    (∀ (N : ℕ) (P : Protocol d), IsNonadaptive P → Succeeds P N ε →
      c * max ((d : ℝ)/ε^2) ((d : ℝ)*Real.sqrt d/ε) ≤ (N : ℝ)) := by sorry

end IncoherentPurity.Adaptive.Supplement
