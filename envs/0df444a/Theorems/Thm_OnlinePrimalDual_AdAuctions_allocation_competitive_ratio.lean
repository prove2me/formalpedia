-- Prove2me | Theorems.Thm_OnlinePrimalDual_AdAuctions_allocation_competitive_ratio
-- name    : OnlinePrimalDual.AdAuctions.allocation_competitive_ratio
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T05:54:37.424521+00:00
-- url     : https://prove2.me/theorems/cdea4c88-d55c-4534-b1e4-a5aea6e60dae
-- title:
--   Theorem 10.1 — the Allocation algorithm's competitive ratio (goal)
-- statement:
--   Given the milestone's dual near-feasibility bound and the fact that each buyer's total
--   accrued bids exceed the budget by at most a factor of `Rmax` (Claim (3)'s "at most one
--   undercharged iteration" consequence), the algorithm's total actual revenue is at least
--   `(1-1/c)(1-Rmax)` times the objective value of any feasible **dual/packing** (Fig. 10.1's
--   maximization LP) solution `y''` — in particular, at least `(1-1/c)(1-Rmax)` times the true
--   offline-optimal ad-auctions revenue (attained at an optimal dual solution, whose value equals
--   the offline optimum by strong LP duality). Revised per moderation (2026-09-21): quantifying
--   over the covering/minimization LP's feasible region instead (as an earlier draft did) is
--   unsound here, since that region is unbounded above — the packing region is the bounded one,
--   and bounded is what a sound universally-quantified lower bound needs.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 212-215, Theorem 10.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue
import Definitions.Def_OnlinePrimalDual_AdAuctions_actualCharge

namespace OnlinePrimalDual.AdAuctions

/-- **Theorem 10.1** (p. 212, PDF p. 123) — the Allocation algorithm's competitive ratio; the goal
of this mission. `wonBids i` lists, in allocation order, the bids of the items actually allocated
to buyer `i`. `h_dual_near_feasible` is the milestone `dual_near_feasible` (Inequality (10.1)).
`h_at_most_one_undercharge` is the book's Claim (3) conclusion (p. 214-215): "there can be at most
one iteration in which a buyer is charged by less than `b(i,j)`... hence
`∑_j b(i,j)y(i,j) ≤ B(i) + maxⱼ{b(i,j)} ≤ B(i)(1+Rmax)`" — the fact that combines with `Rmax` to
turn the raw accrued-bid total into a bound relating it to the *actually charged* revenue.

**Conclusion revised per `CHANGES_REQUESTED.md` (moderation, 2026-09-21).** The book's own exact
statement, "the allocation algorithm is `(1 − 1/c)(1 − Rmax)`-competitive", is formalized via weak
duality against an arbitrary feasible **dual/packing** (Fig. 10.1's maximization LP) solution `y''`
— *not* the covering/minimization LP's feasible region, which is unbounded above (fixing `x''=0`
and taking `z''(j)` arbitrarily large stays feasible there, so quantifying the comparison point
over it made the previous version of this conclusion false: a counterexample with `z''(1)=1000`
forced a revenue bound of `278` against an actual charged revenue of `1`). The dual/packing region
IS bounded (any feasible `y''` has objective value at most `∑ B(i)`), so this universally
quantified statement is sound; at `y'' = y*`, an optimal dual solution (which by strong LP duality
has the same value as the true offline-optimal covering solution, i.e. the true offline-optimal
ad-auctions revenue), it recovers exactly Theorem 10.1's own bound `ALG ≥ ratio · OPT`. Contrast
with `04-framework`'s `algorithm1_competitive_ratio`, a genuinely correct use of the
quantify-over-the-opposite-LP idiom: there the algorithm's own output is itself a
covering/minimization quantity, so quantifying the comparison point over the (unbounded-above)
covering region only makes the bound easier to satisfy as the comparison point grows. Here the
quantity being lower-bounded (`∑ actualCharge`, a revenue/maximization quantity) needs the bounded
LP — the dual/packing one — as its comparison region; pairing it with the covering region (as the
prior draft did) was the wrong pairing. -/
theorem allocation_competitive_ratio {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (wonBids : I → List ℝ)
    (hbids_valid : ∀ i, ∀ bd ∈ wonBids i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i)
    (h_dual_near_feasible : ∀ i : I, buyerX inst i (wonBids i) ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ (revenue inst wonBids i / inst.B i) - 1))
    (h_at_most_one_undercharge : ∀ i : I,
      revenue inst wonBids i ≤ inst.B i * (1 + inst.Rmax)) :
    ∀ y'' : I → M → ℝ, (∀ i j, 0 ≤ y'' i j) →
      (∀ j, ∑ i, y'' i j ≤ 1) →
      (∀ i, ∑ j, inst.b i j * y'' i j ≤ inst.B i) →
      ∑ i, actualCharge inst wonBids i ≥
        (1 - 1 / cParam inst) * (1 - inst.Rmax) *
          (∑ i, ∑ j, inst.b i j * y'' i j) := by sorry

end OnlinePrimalDual.AdAuctions
