-- Prove2me | Theorems.Thm_OnlinePrimalDual_AdAuctions_allocation_competitive_ratio_v2
-- name    : OnlinePrimalDual.AdAuctions.allocation_competitive_ratio_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:52.944766+00:00
-- url     : https://prove2.me/theorems/9555ad25-9c6f-45ef-ab7e-7ee70670b995
-- title:
--   Theorem 10.1 — the Allocation algorithm for ad-auctions is $(1-1/c)(1-R_{\max})$-competitive, $c = (1+R_{\max})^{1/R_{\max}}$
-- statement:
--   Consider the single-slot ad-auctions instance of Section 10.1: buyers $i \in I$ with budgets $B(i) > 0$, items $j \in M$ with bids $b(i,j) \ge 0$, $R_{\max}$ with $b(i,j) \le R_{\max} B(i)$ and $R_{\max} > 0$, and $c = (1+R_{\max})^{1/R_{\max}}$. Items arrive in the order `ord` (a permutation of $M$). Let `alloc` be the algorithm's choice: when item $j$ arrives, it is allocated to a buyer $\texttt{alloc}(j)$ maximizing $b(i,j)(1 - x(i))$ over all buyers $i$, where $x$ is the state after the items preceding $j$ have been processed (ties arbitrary). The run `allocRun inst ord alloc` then does, for each arriving $j$ with $i = \texttt{alloc}(j)$: if $x(i) \ge 1$, nothing; otherwise it charges $i$ for $j$ (the minimum of $b(i,j)$ and $i$'s remaining budget) and updates $x(i) \leftarrow x(i)\big(1 + \tfrac{b(i,j)}{B(i)}\big) + \tfrac{b(i,j)}{(c-1)B(i)}$ (starting from $x = 0$), recording $b(i,j)$ in $i$'s list of charged bids. Then the revenue actually collected, $\sum_i \min\{\sum_{j \text{ charged to } i} b(i,j),\, B(i)\}$, satisfies
--   $$\sum_i \min\Big\{\sum_{j\text{ charged to } i} b(i,j),\, B(i)\Big\} \;\ge\; \Big(1 - \frac1c\Big)(1 - R_{\max}) \sum_i\sum_j b(i,j)\, y''(i,j)$$
--   for every feasible solution $y''$ of the packing LP of Fig. 10.1 ($y'' \ge 0$, $\sum_i y''(i,j) \le 1$ for every item, $\sum_j b(i,j) y''(i,j) \le B(i)$ for every buyer), in particular for the offline optimum: the algorithm is $(1-1/c)(1-R_{\max})$-competitive.
--
--   **Formalization Note.** The retired version took the charged-bid lists as a free variable constrained only by two consequences of the run (inequality (10.1) and Claim (3)'s bound), which the empty run satisfies, so an algorithm allocating nothing was admitted. The new statement computes the charged-bid lists by a definition (`allocRun`) executing the Allocation algorithm — step (2) "if $x(i) \ge 1$ do nothing" and step (3)'s update — on the arrival order, with the argmax rule stated as a hypothesis on the choice function `alloc` evaluated at the algorithm's own state when each item arrives (the book leaves ties arbitrary, and the theorem holds for every tie-breaking), so the theorem is about the algorithm's own output; (10.1) and Claim (3) are no longer assumed. Conventions made explicit: the arrival order is a permutation of the items; the dual variable $z(j)$ of the book's analysis is not needed to state the result and is omitted; competitiveness is stated by weak duality against every feasible packing solution (the retired version's moderator-approved comparison region, whose optimum equals the offline optimum by LP duality); $R_{\max} > 0$ is the platform instance's standing assumption (so $c$ is defined). Correction to the printed source: none.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 212-215, Theorem 10.1 (Section 10.1, the Allocation algorithm)

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue
import Definitions.Def_OnlinePrimalDual_AdAuctions_actualCharge
import Definitions.Def_OnlinePrimalDual_AdAuctions_allocRun_v2

namespace OnlinePrimalDual.AdAuctions

/-- **Theorem 10.1** (Buchbinder & Naor, FnT TCS 2009, p. 212-215) — the Allocation algorithm is
`(1 − 1/c)(1 − Rmax)`-competitive, with `c = (1 + Rmax)^{1/Rmax}`; the goal of this mission.
The run is the algorithm's own: items arrive in the order `ord` (a permutation of `M`), item `j`
is allocated to `alloc j`, which `halloc` requires to be a buyer maximizing `b(i,j)(1 − x(i))`
over all buyers at the moment `j` arrives (`x` being the primal values after the items before
`j` — `ord.takeWhile (· ≠ j)` — have been processed; ties are arbitrary, as in the book), and
`allocRun inst ord alloc` lists the bids each buyer was actually charged for (step (2), "if
`x(i) ≥ 1` do nothing", and step (3)'s update of `x(i)`, both built into `allocRun`). The retired
version let the charged-bid lists be a free variable constrained only by two consequences of the
run ((10.1) and Claim (3)), which the empty run satisfies. The conclusion is the book's statement
via weak duality: the revenue actually collected, `∑ᵢ min(∑ charged bids, B(i))`, is at least
`(1 − 1/c)(1 − Rmax)` times the objective of every feasible solution `y''` of the packing
(maximization) LP of Fig. 10.1, hence at least that fraction of the offline optimum. -/
theorem allocation_competitive_ratio_v2 {I M : Type*} [Fintype I] [Fintype M] [DecidableEq I]
    [DecidableEq M] (inst : AdAuctionsInstance I M) (ord : List M) (hord_nodup : ord.Nodup)
    (hord_mem : ∀ j, j ∈ ord) (alloc : M → I)
    (halloc : ∀ j i,
      inst.b i j * (1 - buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i)) ≤
        inst.b (alloc j) j *
          (1 - buyerX inst (alloc j) (allocRun inst (ord.takeWhile (· ≠ j)) alloc (alloc j)))) :
    ∀ y'' : I → M → ℝ, (∀ i j, 0 ≤ y'' i j) →
      (∀ j, ∑ i, y'' i j ≤ 1) →
      (∀ i, ∑ j, inst.b i j * y'' i j ≤ inst.B i) →
      ∑ i, actualCharge inst (allocRun inst ord alloc) i ≥
        (1 - 1 / cParam inst) * (1 - inst.Rmax) *
          (∑ i, ∑ j, inst.b i j * y'' i j) := by sorry

end OnlinePrimalDual.AdAuctions
