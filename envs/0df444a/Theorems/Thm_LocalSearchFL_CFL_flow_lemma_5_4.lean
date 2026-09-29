-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_flow_lemma_5_4
-- name    : LocalSearchFL.CFL.flow_lemma_5_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:22:39.914773+00:00
-- url     : https://prove2.me/theorems/b7a79521-33fe-460f-b323-1ae27b3015f3
-- title:
--   Lemma 5.4 — routing |N_S(s)| units from each v_s to the sink at cost ≤ cost_s(S) + cost_s(O) + cost_f(O)
-- statement:
--   Let $C$ be a finite set of clients and $F$ a set of facilities in a metric instance with distances $c$, integer capacities $u_i > 0$ and facility costs $f_i \ge 0$. Let $X$ and $O$ be two CFL solutions. Consider the directed graph with a node $v_s$ for every copy $s$ of $X$, a node $w_o$ for every copy $o$ of $O$ and a sink, with an edge $(v_s, w_o)$ of length $c_{so}$ (the distance between the facilities of $s$ and $o$) and an edge $(w_o, \mathrm{sink})$ of length $f_o/u_o$. Then one can route $|N_X(s)|$ units of flow from every $v_s$ to the sink at total cost at most the service costs of both solutions plus the facility cost of $O$: there are nonnegative integers $x_{so}$ (the flow on the path $v_s \to w_o \to \mathrm{sink}$) with $\sum_o x_{so} = |N_X(s)|$ for every $s$ and
--
--   $$\sum_{s}\sum_{o} x_{so}\left(c_{so} + \frac{f_o}{u_o}\right) \le \mathrm{cost}_s(X) + \mathrm{cost}_s(O) + \mathrm{cost}_f(O).$$
--
--   The lemma needs no local optimality. It compares the two solutions through a flow whose cost is then bounded from below by a shortest-path flow in inequality (10).
--
--   **Formalization Note** The graph is complete bipartite plus a sink, so a flow is determined by the amounts $x_{so}$ on the two-edge paths; no graph library is used. The flow is required to be integral, which is what the paper's routing (one unit per client) produces. Here $o$ ranges over the copies of $O$ and $u_o$, $f_o$ are those of the facility of the copy $o$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 560, Lemma 5.4 (graph G defined on p. 559)

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.4**, p. 560: for any two CFL solutions `X` and `O`, in the flow graph with an
edge `(v_s, w_o)` of length `c_{so}` for every copy `s` of `X` and copy `o` of `O`, and an edge
`(w_o, sink)` of length `f_o / u_o`, one can simultaneously route `|N_X(s)|` units of flow
from every `v_s` to the sink at total cost at most `cost_s(X) + cost_s(O) + cost_f(O)`.
Here `x s o` is the (integer-valued) flow on the path `v_s → w_o → sink`. -/
theorem flow_lemma_5_4 {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) :
    ∃ x : Fin X.n → Fin O.n → ℕ,
      (∀ s, ∑ o, x s o = (X.nbhd s).card) ∧
      ∑ s, ∑ o, (x s o : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by sorry

end LocalSearchFL.CFL
