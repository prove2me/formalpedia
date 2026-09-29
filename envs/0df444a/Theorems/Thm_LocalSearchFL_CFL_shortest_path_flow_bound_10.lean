-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_shortest_path_flow_bound_10
-- name    : LocalSearchFL.CFL.shortest_path_flow_bound_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:23:44.54937+00:00
-- url     : https://prove2.me/theorems/b797ef10-a513-4e02-b145-b6e2ae0279b4
-- title:
--   Inequality (10) — the shortest-path flow is bounded by cost_s(S) + cost_s(O) + cost_f(O)
-- statement:
--   Let $C$ be a finite set of clients and $F$ a set of facilities in a metric instance with distances $c$, integer capacities $u_i > 0$ and facility costs $f_i \ge 0$. Let $X$ and $O$ be CFL solutions, $O$ with at least one open copy. Then there is a map $\tau$ from the copies of $X$ to the copies of $O$ such that
--
--   1. for every copy $s$ of $X$, $\tau(s)$ minimizes $c_{so} + f_o/u_o$ over the copies $o$ of $O$ (so $v_s \to w_{\tau(s)} \to \mathrm{sink}$ is a shortest path), and
--   2. writing $T_o = \{ s : \tau(s) = o\}$,
--   $$\mathrm{cost}_s(X) + \mathrm{cost}_s(O) + \mathrm{cost}_f(O) \ \ge\ \sum_{o} \sum_{s \in T_o} |N_X(s)|\left(c_{so} + \frac{f_o}{u_o}\right).$$
--
--   This is inequality (10) of the paper: routing all flow of $v_s$ along its shortest path gives a minimum-cost flow, whose cost is at most that of the flow of Lemma 5.4. The sets $T_o$ are then used in inequality (11).
--
--   **Formalization Note** Every copy of $X$, including copies serving no client, is assigned to some $T_o$; this requires $O$ to have a copy, which holds whenever there is a client. Ties in the minimization are broken arbitrarily (the statement asserts existence of one such $\tau$).
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 560, eq. (10)

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Inequality (10)**, p. 560: for any two CFL solutions `X` and `O` (with `O` opening at
least one copy), route the flow of every `v_s` along a shortest path `v_s → w_{τ(s)} → sink`,
i.e. `τ(s)` minimizes `c_{so} + f_o/u_o` over the copies `o` of `O` (ties broken arbitrarily);
writing `T_o = τ⁻¹(o)`, this flow satisfies
`cost_s(X) + cost_s(O) + cost_f(O) ≥ ∑_{o ∈ O} ∑_{s ∈ T_o} |N_X(s)| (c_{so} + f_o/u_o)`. -/
theorem shortest_path_flow_bound_10 {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) (hO : 0 < O.n) :
    ∃ τ : Fin X.n → Fin O.n,
      (∀ s o, I.cf (X.loc s) (O.loc (τ s)) + f (O.loc (τ s)) / (u (O.loc (τ s)) : ℝ) ≤
        I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ∧
      ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
          ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by sorry

end LocalSearchFL.CFL
