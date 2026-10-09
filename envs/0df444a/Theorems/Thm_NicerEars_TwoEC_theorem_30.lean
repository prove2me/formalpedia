-- Prove2me | Theorems.Thm_NicerEars_TwoEC_theorem_30
-- name    : NicerEars.TwoEC.theorem_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:05.908344+00:00
-- url     : https://prove2.me/theorems/a145f73b-6f6f-4a09-a57f-db5ba976a6f7
-- title:
--   Theorem 30 — every 2-edge-connected graph has a 2ECSS with at most 4/3 LP(G) edges
-- statement:
--   Let $G$ be a 2-edge-connected graph, possibly with parallel edges. Then $G$ has a 2-edge-connected spanning subgraph $F\subseteq E(G)$ with
--
--   $$|F|\le\tfrac43\,\mathrm{LP}(G),\qquad \mathrm{LP}(G)=\min\Bigl\{x(E(G)) : x\in\mathbb R^{E(G)}_{\ge0},\ x(\delta(W))\ge2\ \text{for all}\ \emptyset\ne W\subsetneq V(G)\Bigr\}.$$
--
--   Since $\mathrm{LP}(G)\le\mathrm{OPT}_{2EC}(G)$, this gives a $4/3$-approximation for the minimum 2-edge-connected spanning subgraph problem and bounds the integrality ratio of the cut relaxation by $4/3$.
--
--   **Formalization Note** The paper states an algorithm running in $O(|V(G)|^3)$ time; the formalization states the existence of the subgraph for every input, and the running time is not formalized. "$|F|\le\frac43\mathrm{LP}(G)$" is stated as $|F|\le\frac43x(E(G))$ for every feasible point $x$ of $\mathrm{LP}(G)$, with $F$ chosen before $x$; this is equivalent because $\mathrm{LP}(G)$ is a minimum over the feasible points. $F$ uses each edge of $G$ at most once.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 22, Theorem 30

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

theorem theorem_30 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsTwoEdgeConnected) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by sorry

end NicerEars.TwoEC
