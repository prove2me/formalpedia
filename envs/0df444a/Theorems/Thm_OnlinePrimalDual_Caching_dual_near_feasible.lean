-- Prove2me | Theorems.Thm_OnlinePrimalDual_Caching_dual_near_feasible
-- name    : OnlinePrimalDual.Caching.dual_near_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:47:14.089478+00:00
-- url     : https://prove2.me/theorems/ed333f0c-9325-4e7f-8cff-67f3ad30b268
-- title:
--   Eq. (7.2) — dual near-feasibility (milestone)
-- statement:
--   Let `y` and `z` be the Fractional Caching algorithm's final dual values (non-negative), and
--   assume that whenever the uncapped exponential value would be evaluated (past activation,
--   `c v ≤ dualSum − z`), that uncapped value is itself `≤ 1` (the book's own fact "each `x(p,j)`
--   is never increased to be greater than 1", p. 154-155 — revised per `CHANGES_REQUESTED.md`,
--   2026-09-21, replacing the previous, unsound `h_feasible` hypothesis: `h_feasible` alone does
--   not prevent the *uncapped* value from overshooting `1` arbitrarily far while the *capped*
--   `cachingX` stays feasible). Then, for every primal variable `v`,
--   `(∑_{t|v∈S t} y t) − z v ≤ c v · (1 + ln k)`: the dual solution, scaled down by `1 + ln k`, is
--   feasible.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 155, Eq. (7.2), in the proof of Theorem 7.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance
import Definitions.Def_OnlinePrimalDual_Caching_dualSum
import Definitions.Def_OnlinePrimalDual_Caching_cachingX

namespace OnlinePrimalDual.Caching

/-- **Eq. (7.2)** (p. 155, PDF p. 66), a milestone en route to Theorem 7.1: the algorithm's dual
solution, scaled down by `1 + ln k`, is feasible. `y` and `z` are the algorithm's final dual
values. The conclusion is the book's own simplification of
`x(p,j) = (1/k)exp((1/cp)[(∑y) − z − cp]) ≤ 1` (since every `cachingX` value is capped at `1`,
p. 154-155): `(∑_{t|v∈S t} y t) − z v ≤ c v · (1 + ln k)`, for every primal variable `v`.

**Hypothesis revised per `CHANGES_REQUESTED.md`'s required fix (moderation, 2026-09-21)**: the
prior version took `h_feasible` (primal feasibility of `cachingX`) as its only hypothesis, which
is false as a route to this conclusion — `cachingX` is defined with a `min 1 (…)` cap, so
`h_feasible` says nothing about how far the *uncapped* exponential value overshoots `1`, and a
counterexample (`c=1`, `k=1`, `y=1000`, `z=0`, `rhs=0`) satisfies `h_feasible` while the
conclusion fails (`1000 ≤ 1`). The book derives Eq. (7.2) from "each `x(p,j)` is never increased
to be greater than 1" (p. 154-155) — a fact about the *uncapped* update's own value, not a
consequence of primal feasibility — so `h_uncapped_le_one` replaces `h_feasible` as the
hypothesis that actually encodes it: whenever the uncapped exponential would be evaluated (i.e.
past activation, `c v ≤ dualSum − z`), that value itself is `≤ 1`. -/
theorem dual_near_feasible {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ)
    (hy_nonneg : ∀ t, 0 ≤ y t) (hz_nonneg : ∀ v, 0 ≤ z v)
    (h_uncapped_le_one : ∀ v, inst.c v ≤ dualSum inst y v - z v →
      (1 / (inst.k : ℝ)) * Real.exp ((dualSum inst y v - z v - inst.c v) / inst.c v) ≤ 1) :
    ∀ v : V, dualSum inst y v - z v ≤ inst.c v * (1 + Real.log inst.k) := by sorry

end OnlinePrimalDual.Caching
