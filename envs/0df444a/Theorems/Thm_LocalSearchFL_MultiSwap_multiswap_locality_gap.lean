-- Prove2me | Theorems.Thm_LocalSearchFL_MultiSwap_multiswap_locality_gap
-- name    : LocalSearchFL.MultiSwap.multiswap_locality_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:43:56.987986+00:00
-- url     : https://prove2.me/theorems/f5eb5876-3e39-49f4-a661-b383ec137b8d
-- title:
--   p-swap local search for metric k-median has locality gap at most $3 + 2/p$
-- statement:
--   Consider a metric instance with clients $C$, facilities $F$ and service costs $c_{ji}$ (nonnegative, symmetric, satisfying the triangle inequality), and the k-median cost $\mathrm{cost}(S) = \sum_{j\in C} \min_{i \in S} c_{ji}$ of a nonempty set $S$ of open facilities.
--
--   Let $p \ge 1$ and $k \ge 1$ be integers, and let $S \subseteq F$ with $|S| = k$ be locally optimum for the $p$-swap neighbourhood
--   $$\mathcal B(S) = \{(S \setminus A) \cup B \mid A \subseteq S,\ B \subseteq F,\ |A| = |B| \le p\},$$
--   that is, $\mathrm{cost}(S) \le \mathrm{cost}(S')$ for every $S' \in \mathcal B(S)$. Then for every nonempty set $O \subseteq F$ with $|O| \le k$,
--   $$\mathrm{cost}(S) \le \left(3 + \frac{2}{p}\right) \mathrm{cost}(O).$$
--
--   In the language of local search: the locality gap of the k-median problem with respect to $p$-swaps is at most $3 + 2/p$. As $p$ grows the bound approaches $3$; the paper gives a tight example (§3.5) for $p = 2$.
--
--   **Formalization Note** The bound is stated for every feasible $O$, not only an optimum (the proof never uses optimality), and multiplied out, so that $\mathrm{cost}(O) = 0$ causes no division. The constant is computed in $\mathbb R$ as `3 + 2 / (p : ℝ)`. The case $p = 1$ is Theorem 3.2 of the paper (bound $5$); §3.3 introduces multiswaps for $p > 1$, while the abstract and §3.5 allow every $p \ge 1$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 553, §3.4 (announced §3.3, p. 551)

import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_kmCost

namespace LocalSearchFL.MultiSwap

/-- §3.4, p. 553 (announced §3.3, p. 551): p-swap local search for the metric k-median problem
has locality gap at most `3 + 2/p`. If `p ≥ 1` and `S` is a set of `k` facilities that is locally
optimum for the neighbourhood (3), then `cost(S) ≤ (3 + 2/p) · cost(O)` for every nonempty set
`O` of at most `k` facilities. -/
theorem multiswap_locality_gap {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (p : ℕ) (hp : 1 ≤ p)
    (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsPSwapLocalOpt I p S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ (3 + 2 / (p : ℝ)) * kmCost I O hO := by sorry

end LocalSearchFL.MultiSwap
