-- Prove2me | Theorems.Thm_NisanRonen_Rounding_rounding_error_bound
-- name    : NisanRonen.Rounding.rounding_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:24:50.513409+00:00
-- url     : https://prove2.me/theorems/b5db0915-4e35-49a0-b1cf-d6e8c059555a
-- title:
--   Rounding up to the $\delta$-grid changes the make-span by a factor at most $1 + \delta/a$
-- statement:
--   Let $\delta > 0$, $a > 0$, let $x$ be an allocation of $k$ tasks to $n \ge 1$ agents, and let $\tau$ be a vector of times with $\tau_j \ge a$ for every task $j$. Then
--
--   $$
--   g(x, \tau) \le \hat g(x, \tau) \le \left(1 + \frac{\delta}{a}\right) g(x, \tau).
--   $$
--
--   Rounding every entry up to an integer multiple of $\delta$ adds less than $\delta \le (\delta/a)\,\tau_j$ to each entry. This bound is the quantitative content of choosing $\delta$ "as a function of $a$ and $\epsilon$": with $\delta \le \epsilon a$ the factor is at most $1 + \epsilon$.
--
--   Differences from the source:
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27), unnumbered: "The entries t^i_j are first rounded up to integer multiples of δ (a parameter chosen as a function of a and ϵ)." (proof step; the paper states no bound)

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan

namespace NisanRonen.Rounding

/-- **Rounding error of the make-span** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), p. 192, unnumbered: "The entries t^i_j
are first rounded up to integer multiples of δ (a parameter chosen as a function of a and ϵ)").
If every entry of a time vector `τ` is at least `a > 0` and `δ > 0`, then for every allocation
`x`, rounding up to the δ-grid increases the make-span by a factor of at most `1 + δ / a`:
`g(x, τ) ≤ ĝ(x, τ) ≤ (1 + δ / a) · g(x, τ)`. -/
theorem rounding_error_bound {n k : ℕ} [NeZero n] {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (x : Fin k → Fin n) (τ : Fin k → ℝ) (hτ : ∀ j, a ≤ τ j) :
    makespan x τ ≤ roundedMakespan δ x τ ∧
      roundedMakespan δ x τ ≤ (1 + δ / a) * makespan x τ := by sorry

end NisanRonen.Rounding
