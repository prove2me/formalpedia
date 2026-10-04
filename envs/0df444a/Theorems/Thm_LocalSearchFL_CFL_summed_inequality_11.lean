-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_summed_inequality_11
-- name    : LocalSearchFL.CFL.summed_inequality_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:24:12.553342+00:00
-- url     : https://prove2.me/theorems/2aa9c391-cad8-4896-bfc7-68fd805eca63
-- title:
--   Inequality (11) — Σ_o f_o + Σ_o Σ_{s∈T_o} |N_S(s)|(c_so + f_o/u_o) ≥ cost_f(S)
-- statement:
--   Let $C$ be a finite set of clients and $F$ a set of facilities in a metric instance with distances $c$, integer capacities $u_i > 0$ and facility costs $f_i \ge 0$. Let $X$ be a locally optimum CFL solution for the neighbourhood (9) and $O$ any CFL solution. For every map $\tau$ from the copies of $X$ to the copies of $O$, with $T_o = \{ s : \tau(s) = o \}$,
--
--   $$\sum_{o} f_o + \sum_{o}\sum_{s \in T_o} |N_X(s)|\left(c_{so} + \frac{f_o}{u_o}\right) \ \ge\ \sum_{o}\sum_{s\in T_o} f_s = \mathrm{cost}_f(X).$$
--
--   Here $o$ ranges over the copies of $O$, $f_o$ and $u_o$ are the cost and capacity of the facility of $o$, and $f_s$ is the cost of the facility of the copy $s$ of $X$. This is inequality (11): Lemma 5.2 applied to $T_o$ and (the facility of) $o$, weakened by $\lceil x \rceil \le 1 + x$, and summed over $o$. With (10) it bounds the facility cost of $X$.
--
--   **Formalization Note** The statement is the conjunction of the inequality and the identity $\sum_o\sum_{s\in T_o} f_s = \mathrm{cost}_f(X)$ printed with it. It holds for every $\tau$, not only for the shortest-path one. Unlike Lemma 5.2, no hypothesis that there is a client is needed.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 560, eq. (11)

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Inequality (11)**, p. 560: let `X` be a locally optimum CFL solution
and `O` any CFL solution. For every map `τ` from the copies of `X` to the copies of
`O`, writing `T_o = τ⁻¹(o)`,
`∑_{o ∈ O} f_o + ∑_{o ∈ O} ∑_{s ∈ T_o} |N_X(s)| (c_{so} + f_o/u_o) ≥ ∑_{o ∈ O} ∑_{s ∈ T_o} f_s`,
and the right-hand side equals `cost_f(X)`. -/
theorem summed_inequality_11 {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u)
    (τ : Fin X.n → Fin O.n) :
    ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), f (X.loc s) ≤
      ∑ o, f (O.loc o) +
        ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
          ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ∧
    ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o), f (X.loc s) = costF f X := by sorry

end LocalSearchFL.CFL
