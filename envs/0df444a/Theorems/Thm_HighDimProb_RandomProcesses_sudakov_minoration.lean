-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_sudakov_minoration
-- name    : HighDimProb.RandomProcesses.sudakov_minoration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T22:59:55.485968+00:00
-- url     : https://prove2.me/theorems/3cbe87f3-71cb-4d22-8595-f4db098ede91
-- title:
--   Theorem 7.4.1 — Sudakov's minoration inequality
-- statement:
--   This is **Sudakov's minoration inequality**, a lower bound on the expected supremum of a
--   Gaussian process purely in terms of the geometry (metric entropy) of its index set under the
--   canonical metric — the first result connecting the probabilistic size of a Gaussian process to
--   covering numbers, continued systematically in Chapter 8.
--
--   Let $(X_t)_{t\in T}$ be a mean zero Gaussian process on a common probability space, indexed by
--   an arbitrary (possibly uncountable) nonempty set $T$, and let $d$ be its canonical metric
--   (`CanonicalMetric`, Eq. (7.13)). Then, for every $\varepsilon \ge 0$ at which the covering
--   number $N(T,d,\varepsilon)$ (`CoveringNumber`) is finite, say equal to $N\in\mathbb N$ — the
--   case the book's own proof of this theorem establishes, deferring $N(T,d,\varepsilon)=\infty$ to
--   a separate exercise (7.4.2) — there is an absolute constant $c>0$ with
--
--   $$
--   E \sup_{t\in T} X_t \;\ge\; c\,\varepsilon\,\sqrt{\log N}.
--   $$
--
--   In words: an index set that is metrically large at scale $\varepsilon$ (needs many
--   $\varepsilon$-balls to cover) forces the process to fluctuate by at least that much.
--
--   **Formalization Note** `E sup` is `ProcessESup`. The covering number is bounded via a case
--   hypothesis `coveringNumber (canonicalMetric P X) ε = (N : ℕ∞)` rather than by casing on the
--   infinite value inside the conclusion, so `T` itself is never required to be finite or
--   countable — only the covering number at the fixed scale `ε` in play.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 170, Theorem 7.4.1

import Mathlib
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
import Definitions.Def_HighDimProb_RandomProcesses_CanonicalMetric
import Definitions.Def_HighDimProb_RandomProcesses_CoveringNumber

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomProcesses

/-- **Theorem 7.4.1** (Sudakov's minoration inequality), Vershynin, *High-Dimensional
Probability* (2018), p. 170 (PDF p. 178).

Let `(X_t)_{t∈T}` be a mean zero Gaussian process on an arbitrary (possibly uncountable)
nonempty index set `T`, and let `d` be its canonical metric (`canonicalMetric`, Eq. (7.13)).
Then, for every `ε ≥ 0` at which the covering number `N(T, d, ε)` is finite (equal to some
`N : ℕ`) — the book's own proof of this theorem, p. 170–171 (PDF p. 178–179), establishes
exactly this case, deferring `N(T, d, ε) = ∞` to Exercise 7.4.2 — we have `E sup_{t∈T} X_t ≥
c·ε·√(log N)` for an absolute constant `c > 0`. -/
theorem sudakov_minoration :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [Nonempty T] (X : T → Ω → ℝ)
        (hXG : IsGaussianProcess X P) (hXmean : ∀ t, ∫ ω, X t ω ∂P = 0)
        (ε : ℝ), 0 ≤ ε →
        ∀ (N : ℕ), coveringNumber (canonicalMetric P X) ε = (N : ℕ∞) →
        ((c * ε * Real.sqrt (Real.log N) : ℝ) : EReal) ≤ processESup P X := by sorry

end HighDimProb.RandomProcesses
