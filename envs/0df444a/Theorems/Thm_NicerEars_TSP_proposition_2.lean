-- Prove2me | Theorems.Thm_NicerEars_TSP_proposition_2
-- name    : NicerEars.TSP.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:49.944914+00:00
-- url     : https://prove2.me/theorems/9b58c1bc-4bba-4b7a-93d2-fdb7d04e2dc4
-- title:
--   Proposition 2 — OPT(G) ≥ OPT₂EC(G) ≥ LP(G) ≥ |V(G)|
-- statement:
--   **Proposition 2.** Let $G$ be a connected graph with at least two vertices. Then
--
--   $$\mathrm{OPT}(G)\ \ge\ \mathrm{OPT}_{2EC}(G)\ \ge\ \mathrm{LP}(G)\ \ge\ |V(G)|.$$
--
--   Here $\mathrm{OPT}(G)$ is the minimum cardinality of a tour (a connected $\emptyset$-join in $2G$), $\mathrm{OPT}_{2EC}(G)$ the minimum number of edges of a 2-edge-connected spanning multi-subgraph of $G$, and $\mathrm{LP}(G)=\min\{x(E(G)): x\ge 0,\ x(\delta(W))\ge 2 \text{ for all } \emptyset\ne W\subsetneq V(G)\}$.
--
--   The chain makes $\mathrm{LP}(G)$ a lower bound for both the graphic TSP and the 2-edge-connected subgraph problem, so a tour of size at most $\rho\,\mathrm{LP}(G)$ is a $\rho$-approximation.
--
--   **Formalization Note.** The two LP inequalities are stated through feasible points: some LP-feasible $x$ has $x(E(G))\le\mathrm{OPT}_{2EC}(G)$, and every LP-feasible $x$ has $x(E(G))\ge|V(G)|$. The hypothesis $|V(G)|\ge 2$ is added: on one vertex there is no cut constraint, so $\mathrm{LP}(G)=0<1=|V(G)|$ and the printed last inequality fails.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5, Proposition 2

import Mathlib
import Definitions.Def_NicerEars_TSP_Setting

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proposition 2, p. 5: for every connected graph G (with at least two vertices),
OPT(G) ≥ OPT_2EC(G) ≥ LP(G) ≥ |V(G)|. The LP inequalities are stated through feasible points:
some LP(G)-feasible x has x(E(G)) ≤ OPT_2EC(G), and every LP(G)-feasible x has x(E(G)) ≥ |V(G)|. -/
theorem proposition_2 (G : Graph V E) (hG : G.IsConnected) (hV : 2 ≤ Fintype.card V) :
    G.OPT2EC ≤ G.OPT ∧
    (∃ x : E → ℝ, G.LPFeasible x ∧ ∑ e, x e ≤ (G.OPT2EC : ℝ)) ∧
    ∀ x : E → ℝ, G.LPFeasible x → (Fintype.card V : ℝ) ≤ ∑ e, x e := by sorry

end NicerEars.TSP
