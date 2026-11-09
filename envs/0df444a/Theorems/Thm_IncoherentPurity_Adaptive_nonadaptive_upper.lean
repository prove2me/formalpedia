-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_nonadaptive_upper
-- name    : IncoherentPurity.Adaptive.nonadaptive_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:03.036302+00:00
-- url     : https://prove2.me/theorems/5bf7d49c-9bfb-4111-87ef-5e019e30fb5b
-- title:
--   Theorem 3.1 — Non-adaptive upper bound
-- statement:
--   There is an absolute constant $C>0$ such that for every integer $d\ge2$ and $0<\varepsilon\le1/4$, one non-adaptive single-copy protocol succeeds for every state using a fixed budget $N$ with
--
--   $$N\le C\max\{d^{3/2}/\varepsilon,d/\varepsilon^2\}.$$
--
--   Success has relative error $\varepsilon$ and probability at least $2/3$. Shared parameter-independent randomness is allowed.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Theorem 3.1, PDF p.9 = printed p.9

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Theorem 3.1, PDF p.9, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem nonadaptive_upper : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
  ∃ (N : ℕ) (P : Protocol d), IsNonadaptive P ∧ Succeeds P N ε ∧
    (N : ℝ) ≤ C * max ((d : ℝ)*Real.sqrt d/ε) ((d : ℝ)/ε^2) := by sorry

end IncoherentPurity.Adaptive
