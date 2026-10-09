-- Prove2me | Theorems.Thm_NicerEars_TwoEC_proposition_2
-- name    : NicerEars.TwoEC.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:51.067628+00:00
-- url     : https://prove2.me/theorems/4962a35e-1095-43ef-974b-b1e8a7fc23e3
-- title:
--   Proposition 2 — OPT(G) ≥ OPT₂EC(G) ≥ LP(G) ≥ |V(G)| for connected G with at least two vertices
-- statement:
--   Let $G$ be a connected graph (parallel edges allowed) with at least two vertices. Then
--
--   $$\mathrm{OPT}(G)\ \ge\ \mathrm{OPT}_{2EC}(G)\ \ge\ \mathrm{LP}(G)\ \ge\ |V(G)|,$$
--
--   where $\mathrm{OPT}(G)$ is the minimum size of a tour (a connected multi-subgraph of $2G$ with all degrees even), $\mathrm{OPT}_{2EC}(G)$ the minimum size of a 2-edge-connected spanning multi-subgraph of $G$, and $\mathrm{LP}(G)$ the optimum of the cut relaxation $\min\{x(E(G)) : x\ge0,\ x(\delta(W))\ge2 \text{ for } \emptyset\ne W\subsetneq V(G)\}$.
--
--   The chain makes $\mathrm{LP}(G)$ a lower bound for both the graphic TSP and the 2ECSS problem, and $|V(G)|$ a lower bound for $\mathrm{LP}(G)$.
--
--   **Formalization Note** The hypothesis $|V(G)|\ge2$ is added: for the one-vertex graph there is no cut constraint, $\mathrm{LP}(G)=0<1=|V(G)|$, so the printed inequality $\mathrm{LP}(G)\ge|V(G)|$ fails there. All values are compared as real numbers.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5, Proposition 2

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

theorem proposition_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsConnected) (hV : 2 ≤ Fintype.card V) :
    (G.OPT2EC : ℝ) ≤ G.OPTTour ∧ G.lpValue ≤ G.OPT2EC ∧ (Fintype.card V : ℝ) ≤ G.lpValue := by sorry

end NicerEars.TwoEC
