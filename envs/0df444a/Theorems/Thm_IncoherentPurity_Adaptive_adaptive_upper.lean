-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_adaptive_upper
-- name    : IncoherentPurity.Adaptive.adaptive_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:01.457038+00:00
-- url     : https://prove2.me/theorems/a6d9fc0f-c634-4a61-9680-214a4d0c5c3e
-- title:
--   Theorem 4.1 — Adaptive upper bound
-- statement:
--   There is an absolute constant $C>0$ such that for every $d\ge1$ and every positive real $\varepsilon$, an adaptive incoherent protocol succeeds for every state with a fixed budget satisfying
--
--   $$N\le C\left(d^2/\varepsilon+\sqrt d/\varepsilon^2\right).$$
--
--   Success means relative error at most $\varepsilon$ with probability at least $2/3$. The large-precision regime is included; zero output suffices when $\varepsilon\ge1$.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Theorem 4.1, PDF p.12 = printed p.12

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Theorem 4.1, PDF p.12, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem adaptive_upper : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → ∀ ε : ℝ, 0 < ε →
  ∃ (N : ℕ) (P : Protocol d), Succeeds P N ε ∧
    (N : ℝ) ≤ C * ((d : ℝ)^2/ε + Real.sqrt d/ε^2) := by sorry

end IncoherentPurity.Adaptive
