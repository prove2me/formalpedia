-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_4
-- name    : MPBSelect.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:49:04.990265+00:00
-- url     : https://prove2.me/theorems/43c2f58f-8815-4eb7-bc19-57d2d6760955
-- title:
--   Theorem 4 — Algorithm 1 finds the MPB almost surely
-- statement:
--   Consider a complete stochastic run of Algorithm 1: every pair receives the positive warm start; posterior means are updated from independent Gaussian outputs; conditional optima and the MPB are recomputed with the paper's tie rule; the minimum entry of $W_n\circ G_n$ is selected; and the global-balance comparison determines the sampled solution.
--
--   **Theorem 4.** With probability one, the tie-broken estimated MPB equals the unique true MPB at every sufficiently large iteration.
--
--   This is the almost-sure consistency claim printed as “Algorithm 1 finds the MPB almost surely as $n$ increases.”
--
--   Differences from the source:
--   - encoding: Algorithm 1 and Model (4) are given operationally → a filtered run relation states initialization, posterior updates, tie breaking, sampling decisions, count recursion and fresh conditional Gaussian laws; reason: it is the same adaptive stochastic algorithm with every implicit run component made explicit
--   - encoding: “finds the MPB almost surely as $n$ increases” → eventual equality of the finite-valued estimator and $i^*$ almost surely; reason: convergence to a point in a finite discrete solution set is equivalent to eventual equality
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 4 and Algorithm 1, pp.22-23; Models (4)-(5), pp.8-9

import Mathlib
import Definitions.Def_MPBSelect_Supplement_Sequential

open Filter MeasureTheory

namespace MPBSelect.Supplement

/-- **Theorem 4 (almost-sure consistency of Algorithm 1).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 4,
p.22, for the complete run relation of Algorithm 1 on pp.22--23.

The tie-broken MPB returned by Algorithm 1 equals the true unique MPB eventually, almost surely. -/
theorem theorem_4 {k B : ℕ} (P : MPBSelect.Problem k B) (D : SequentialData P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (istar : ℕ → Ω → Fin k) (selected decision : ℕ → Ω → Fin k × Fin B)
    (hRun : IsAlgorithm1Run P D μ F Y N istar selected decision) :
    ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, istar t ω = P.istar := by sorry

end MPBSelect.Supplement
