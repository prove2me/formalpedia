-- Prove2me | Theorems.Thm_NisanRonen_Rounding_rounded_optimum_approx
-- name    : NisanRonen.Rounding.rounded_optimum_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:25:40.533772+00:00
-- url     : https://prove2.me/theorems/ff884415-4e64-4a32-bc60-41640d13e8f8
-- title:
--   An optimum of the rounded problem is a $(1 + \delta/a)$-approximation
-- statement:
--   Let $0 < a < b$, $\delta > 0$, and let $t = (t^i_j)$ be a type matrix of $n \ge 1$ agents and $k$ tasks with $a \le t^i_j \le b$. If the allocation $x$ minimizes the rounded make-span,
--   $$
--   \hat g\big(x, \mathrm{corr}^*(x,t)\big) \le \hat g\big(y, \mathrm{corr}^*(y,t)\big) \quad \text{for every allocation } y,
--   $$
--   then for every allocation $y$
--   $$
--   g\big(x, \mathrm{corr}^*(x,t)\big) \le \left(1 + \frac{\delta}{a}\right) g\big(y, \mathrm{corr}^*(y,t)\big).
--   $$
--
--   With $\delta \le \epsilon a$ this is the statement that the solution of the rounded problem is a $1+\epsilon$ approximation of the original one.
--
--   Differences from the source:
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - generalization: a 1 + ϵ approximation, for δ chosen as a function of a and ϵ → the explicit factor 1 + δ/a, for every δ > 0; reason: the Lean statement holds for every grid step; taking δ ≤ ϵa gives the source's 1 + ϵ
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27), unnumbered: "The solution of the rounded problem is shown to be a 1 + ϵ approximation of the original one."

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan
import Definitions.Def_NisanRonen_Rounding_corrStar

namespace NisanRonen.Rounding

/-- **An optimum of the rounded problem approximates the original optimum** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001),
p. 192, unnumbered: "The solution of the rounded problem is shown to be a 1 + ϵ approximation of
the original one"). In the bounded problem (`0 < a < b`, all entries of the type matrix `t` in
`[a, b]`) with grid `δ > 0`, let `x` minimize the rounded make-span `ĝ(·, corr*(·, t))`. Then for
every allocation `y`, `g(x, corr*(x, t)) ≤ (1 + δ / a) · g(y, corr*(y, t))`.

**Formalization Note** The factor is the explicit `1 + δ / a`; with `δ ≤ ϵ a` (δ a function of
`a` and `ϵ`, as on p. 192) it is at most `1 + ϵ`. -/
theorem rounded_optimum_approx {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (x : Fin k → Fin n)
    (hx : ∀ y : Fin k → Fin n, roundedMakespan δ x (corrStar x t) ≤ roundedMakespan δ y (corrStar y t)) :
    ∀ y : Fin k → Fin n, makespan x (corrStar x t) ≤ (1 + δ / a) * makespan y (corrStar y t) := by sorry

end NisanRonen.Rounding
