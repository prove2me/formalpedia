-- Prove2me | Theorems.Thm_NicerEars_TwoEC_tour_to_twoECSS
-- name    : NicerEars.TwoEC.tour_to_twoECSS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:48.588352+00:00
-- url     : https://prove2.me/theorems/072cef67-357c-4c86-aa1f-9534a918e4ac
-- title:
--   §1, p. 3 — a tour in a 2-edge-connected graph gives a 2ECSS with at most as many edges
-- statement:
--   Let $G$ be a 2-edge-connected graph and let $F$ be a tour of $G$, that is, a multi-subgraph of $2G$ that is connected on $V(G)$ and in which every vertex has even degree. Then there is a 2-edge-connected spanning subgraph $F'\subseteq E(G)$ (each edge used at most once) with
--
--   $$|F'|\le|F|.$$
--
--   This lets any tour construction be used for the 2ECSS problem; in the proof of Theorem 30 it converts the tour of Theorem 24 into a 2ECSS.
--
--   **Formalization Note** The tour lives in $2G$ (edge type $E\times\{0,1\}$), while $F'$ is a set of edges of $G$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, §1, p. 3, "Note that any tour in a 2-edge-connected graph G gives rise to a 2ECSS of G with at most the same number of edges."

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

theorem tour_to_twoECSS {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsTwoEdgeConnected) (F : Finset (E × Fin 2)) (hF : G.IsTour F) :
    ∃ F' : Finset E, G.IsTwoECSpanning F' ∧ #F' ≤ #F := by sorry

end NicerEars.TwoEC
