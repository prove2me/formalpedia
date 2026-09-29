-- Prove2me | Theorems.Thm_OnlinePrimalDual_Caching_algorithm_competitive_ratio
-- name    : OnlinePrimalDual.Caching.algorithm_competitive_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:49:10.237453+00:00
-- url     : https://prove2.me/theorems/458ff838-fdf9-4036-9874-5beada13bd3c
-- title:
--   Theorem 7.1 — the fractional caching algorithm's competitive ratio (goal)
-- statement:
--   Let `y`, `z` be the algorithm's final dual values (non-negative) and `cachingX inst y z` the
--   resulting primal/caching values, assume the primal solution is feasible, assume the
--   algorithm's own complementary-slackness behavior (`h_comp_slack`, `h_comp_slack_z`), and
--   assume the dual near-feasibility bound of Eq. (7.2) (the milestone above, now correctly
--   derived — see `dual_near_feasible`). Then the algorithm's primal cost is at most
--   `2(1 + ln k)` times the cost of any feasible offline caching solution respecting the same
--   box constraint `0 ≤ x'' ≤ 1` the primal LP itself imposes — the book's own statement, "the
--   algorithm is 2(1 + ln k)-competitive." Revised per `CHANGES_REQUESTED.md` (moderation,
--   2026-09-21): the previous version compared costs directly, which a counterexample
--   (`rhs ≡ 0`, `x'' := 0`) showed unsound since this chapter's `rhs` can be non-positive; the
--   proof now routes through the actual dual objective via the two new auxiliary items
--   `weak_duality` and `cost_le_twice_dual`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 154-157, Theorem 7.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance
import Definitions.Def_OnlinePrimalDual_Caching_dualSum
import Definitions.Def_OnlinePrimalDual_Caching_cachingX
import Definitions.Def_OnlinePrimalDual_Caching_DualObjective

namespace OnlinePrimalDual.Caching

/-- **Theorem 7.1** (p. 154, PDF p. 65) — the fractional caching algorithm's competitive ratio;
the goal of this mission. `y`, `z` are the algorithm's final dual values; `cachingX inst y z` is
the corresponding primal/caching vector by the algorithm's own closed-form update rule (steps
(3)-(4)). `h_feasible` is Claim (1), that the algorithm's primal solution is feasible (p. 154-155);
`h_comp_slack`/`h_comp_slack_z` are the algorithm's own complementary-slackness behavior (see
`cost_le_twice_dual`'s doc-comment); `h_dual_near_feasible` is the milestone `dual_near_feasible`
(Eq. (7.2)) — together these characterize a completed run. The conclusion is the book's own exact
statement: "the algorithm is 2(1 + ln k)-competitive", against any offline-feasible comparison
solution `x''` **respecting the same box constraint the primal LP itself imposes**
(`0 ≤ x'' ≤ 1`, p. 150) — the proof now routes through `DualObjective` (via `cost_le_twice_dual`
and `weak_duality`, both new items in this pass) rather than comparing `cachingX`'s cost directly
against `x''`'s: `04-framework`'s direct-comparison shortcut is unsound here because this
chapter's `rhs` can be non-positive (`CHANGES_REQUESTED.md`'s required fix, moderation
2026-09-21 — a counterexample with `rhs ≡ 0`, `x'' := 0` broke the previous, direct-comparison
statement of this theorem). -/
theorem algorithm_competitive_ratio {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ)
    (hy_nonneg : ∀ t, 0 ≤ y t) (hz_nonneg : ∀ v, 0 ≤ z v)
    (h_feasible : ∀ t, inst.rhs t ≤ ∑ v ∈ inst.S t, cachingX inst y z v)
    (h_comp_slack : ∀ t, 0 < y t → inst.rhs t = ∑ v ∈ inst.S t, cachingX inst y z v)
    (h_comp_slack_z : ∀ v, 0 < z v → cachingX inst y z v = 1)
    (h_dual_near_feasible : ∀ v : V, dualSum inst y v - z v ≤ inst.c v * (1 + Real.log inst.k)) :
    ∀ x'' : V → ℝ, (∀ v, 0 ≤ x'' v) → (∀ v, x'' v ≤ 1) →
      (∀ t, inst.rhs t ≤ ∑ v ∈ inst.S t, x'' v) →
      ∑ v, inst.c v * cachingX inst y z v ≤
        2 * (1 + Real.log inst.k) * ∑ v, inst.c v * x'' v := by sorry

end OnlinePrimalDual.Caching
