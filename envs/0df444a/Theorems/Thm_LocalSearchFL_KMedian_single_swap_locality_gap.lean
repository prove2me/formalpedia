-- Prove2me | Theorems.Thm_LocalSearchFL_KMedian_single_swap_locality_gap
-- name    : LocalSearchFL.KMedian.single_swap_locality_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:13:00.467989+00:00
-- url     : https://prove2.me/theorems/ad7b0390-920c-4632-87ce-65d1d9ae5748
-- title:
--   Theorem 3.2 — single-swap local search for metric k-median has locality gap at most 5
-- statement:
--   Consider a metric instance with a finite set of clients $C$, a finite set of facilities $F$ and service costs $c_{ji}$ (nonnegative, symmetric, satisfying the triangle inequality), and let $k \ge 1$. For a nonempty $S \subseteq F$ let $\mathrm{cost}(S) = \sum_{j\in C}\min_{i\in S} c_{ji}$.
--
--   Let $S \subseteq F$ be a set of exactly $k$ facilities that is locally optimum for single swaps: $\mathrm{cost}(S) \le \mathrm{cost}(S - s + s')$ for every $s \in S$ and $s' \in F \setminus S$. Then for every nonempty set $O \subseteq F$ of at most $k$ facilities,
--   $$\mathrm{cost}(S) \le 5 \cdot \mathrm{cost}(O).$$
--
--   In the paper's words: a local search procedure for the metric k-median problem with the neighbourhood structure $\mathcal B(S) = \{S - \{s\} + \{s'\} \mid s \in S\}$ has a locality gap of at most 5. Taking $O$ to be an optimal solution, every local optimum of the single-swap local search is a 5-approximation.
--
--   **Formalization Note** The local search starts from $k$ facilities and swaps preserve the size, so the local optimum has exactly $k$ facilities; $O$ ranges over every feasible solution (the proof never uses optimality of $O$), which is stronger than comparing with an optimum. The bound is multiplied out, so it is meaningful when $\mathrm{cost}(O) = 0$. The hypothesis $k \ge 1$ is expressed by the nonemptiness of $S$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 551, Theorem 3.2 (neighbourhood from §3.1, p. 548; locality gap p. 545; local optimality p. 547)

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_kmCost

namespace LocalSearchFL.KMedian

/-- Theorem 3.2 (p. 551): single-swap local search for the metric k-median problem has locality
gap at most 5. If `S` is a set of `k` facilities that is locally optimum for single swaps, then
`cost(S) ≤ 5 · cost(O)` for every nonempty set `O` of at most `k` facilities. -/
theorem single_swap_locality_gap {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsSwapLocalOpt I S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ 5 * kmCost I O hO := by sorry

end LocalSearchFL.KMedian
