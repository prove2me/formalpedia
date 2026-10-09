-- Prove2me | Theorems.Thm_NicerEars_TSP_theorem_29
-- name    : NicerEars.TSP.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:02.11539+00:00
-- url     : https://prove2.me/theorems/7a0fbe24-f555-4152-9a1f-f1f9af96bcec
-- title:
--   Theorem 29 — every connected graph has a tour with at most 7/5 LP(G) edges
-- statement:
--   **Theorem 29.** For every connected graph $G$ there is a tour $F$ (a connected $\emptyset$-join in $2G$, i.e. a connected multi-subgraph of $2G$ in which every vertex has even degree) with
--
--   $$|F|\ \le\ \tfrac75\,\mathrm{LP}(G),\qquad \mathrm{LP}(G)=\min\Big\{x(E(G)) : x\ge 0,\ x(\delta(W))\ge 2\ \text{for all}\ \emptyset\ne W\subsetneq V(G)\Big\}.$$
--
--   Since $\mathrm{LP}(G)\le\mathrm{OPT}(G)$ (Proposition 2), this gives a $\frac75$-approximation for the graphic TSP (the TSP in the shortest-path metric of an unweighted graph), and bounds the integrality ratio of the 2-edge-connected subgraph relaxation for graphic TSP by $\frac75$.
--
--   **Formalization Note.** The paper states an algorithm running in $O(|V(G)|^3)$ time; the formalization states the existence of the tour and does not formalize the algorithm or its running time. "$|F|\le\frac75\mathrm{LP}(G)$" is stated as $|F|\le\frac75x(E(G))$ for every LP-feasible $x$, with the tour chosen before $x$; this is equivalent because $\mathrm{LP}(G)$ is the minimum over feasible points. Graphs may have parallel edges, as in the paper.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 21, Theorem 29

import Mathlib
import Definitions.Def_NicerEars_TSP_Setting

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 29, p. 21: every connected graph G has a tour of cardinality at most 7/5 LP(G),
stated against every feasible point x of LP(G). -/
theorem theorem_29 (G : Graph V E) (hG : G.IsConnected) :
    ∃ F : Finset (E × Fin 2), G.IsTour F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 7 / 5 * ∑ e, x e := by sorry

end NicerEars.TSP
