-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_eq30_eventually_below_fare
-- name    : NestedSeatAlloc.IntPolicy.eq30_eventually_below_fare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:18:27.070987+00:00
-- url     : https://prove2.me/theorems/9852d19d-dcdf-4154-92bd-c1b0e9510afb
-- title:
--   (30), p. 133 — for s large enough, δ₊ER_{k+1}[s; p; X] < f_{k+2}
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space and strictly decreasing fares $f_1 > f_2 > \cdots$, all positive. Let $p$ be a protection-level policy ($p_k \ge 0$) and fix $k \ge 1$. Then there is a number of seats $s \ge 0$ at which the right derivative of $ER_{k+1}[\,\cdot\,; p; X]$ exists and
--   $$\delta_+ ER_{k+1}[s; p; X] < f_{k+2}.$$
--
--   Together with the convention $\delta_- ER_{k+1}[0; p; X] = +\infty > f_{k+2}$, this places $f_{k+2}$ strictly between a right derivative and a left derivative, which is the hypothesis of the covering property used to choose $p^*_{k+1}$.
--
--   **Formalization Note** Positivity of the fares is added ($f_k > 0$ for $k \ge 1$): with $f_{k+2} \le 0$ the claim can fail, and the paper's fares are average revenues. The page derives (30) for integer-valued demand "by recursive application of (28) and (29)"; the statement holds for any nonnegative real demands and any policy, and integrality is not assumed, which makes it stronger. The page writes "for each $k = 2, 3, \dots$"; the proof of Theorem 2 uses (30) for $ER_{k+1}$ at every $k \ge 1$ (for $k = 0$ it is the separately stated $\delta_+ ER_1[s] = f_1\Pr[X_1 > s] < f_2$), so it is stated for every $k \ge 1$. The equality $\infty = \delta_- ER_{k+1}[0; p; x]$ of (30) is a convention, not a claim, and is not formalized.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), (30), proof of Theorem 2, p. 133

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

/-- (30), p. 133: with positive fares, for every protection-level policy `p` and every `k ≥ 1` there is a
number of seats `s ≥ 0` large enough that `δ₊ER_{k+1}[s; p; X] < f_{k+2}`. -/
theorem eq30_eventually_below_fare {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (hpos : ∀ k, 1 ≤ k → 0 < f k)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ s, 0 ≤ s ∧
      ∃ r, HasDerivWithinAt (expRevenue P X f p (k + 1)) r (Set.Ici s) s ∧ r < f (k + 2) := by sorry

end NestedSeatAlloc.IntPolicy
