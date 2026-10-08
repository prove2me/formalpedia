-- Prove2me | Theorems.Thm_GeometryOfGraphs_FlowCut_weak_duality_cut
-- name    : GeometryOfGraphs.FlowCut.weak_duality_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:57:52.456277+00:00
-- url     : https://prove2.me/theorems/bc1f6012-d4eb-48a5-bbfe-ba8c461b2232
-- title:
--   §4, p. 226 — every concurrent flow value λ satisfies λ ≤ Cap(S)/Dem(S)
-- statement:
--   Let $N$ be a multicommodity flow network on a finite vertex set $V$ with capacities $C$ and commodities $(s_\mu, t_\mu, D_\mu)_{\mu=1}^k$. If there is a feasible concurrent flow of value $\lambda \ge 0$, then for every $S \subseteq V$
--   $$\lambda \cdot \mathrm{Dem}(S) \le \mathrm{Cap}(S).$$
--
--   This is the "trivial upper bound" of the paper: every cut bounds the concurrent flow, $\lambda \le \mathrm{Cap}(S)/\mathrm{Dem}(S)$. It is the easy direction of the flow–cut gap that Theorem 4.1 controls, and it shows that $\mathrm{maxflow}$ is finite whenever some cut separates a pair with positive demand.
--
--   **Formalization Note** The inequality is cross-multiplied, so it also covers $\mathrm{Dem}(S) = 0$.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 226, Section 4, second paragraph

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- §4, p. 226: "Obviously, λ ≤ Cap(S)/Dem(S) for every S." Every feasible concurrent flow value
`lam ≥ 0` satisfies `lam * Dem(S) ≤ Cap(S)` for every vertex set `S` (cross-multiplied). -/
theorem weak_duality_cut {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (f : Fin N.k → V → V → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (hf : N.IsFeasibleFlow f lam)
    (S : Finset V) :
    lam * N.Dem S ≤ N.Cap S := by sorry

end GeometryOfGraphs.FlowCut
