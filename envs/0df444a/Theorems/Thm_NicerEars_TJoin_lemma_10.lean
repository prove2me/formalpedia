-- Prove2me | Theorems.Thm_NicerEars_TJoin_lemma_10
-- name    : NicerEars.TJoin.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:03.395987+00:00
-- url     : https://prove2.me/theorems/11d882cc-fcb5-435d-8e72-dbc002db315d
-- title:
--   Lemma 10 — every 2-vertex-connected graph has a nice ear-decomposition
-- statement:
--   For any 2-vertex-connected graph $G$ there exists a nice ear-decomposition: one with $\varphi(G)$ even ears, all of whose short (2- and 3-) ears are pendant, and in which internal vertices of different short ears are non-adjacent.
--
--   Nice ear-decompositions are the starting point of all three approximation algorithms of the paper.
--
--   **Formalization Note.** The running time $O(|V(G)||E(G)|)$ is not formalized. "2-vertex-connected" means 2-edge-connected without a cut vertex (see the Setting item).
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 9, Lemma 10

import Mathlib
import Definitions.Def_NicerEars_TJoin_Ears

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lemma 10 (p. 9), existence part: every 2-vertex-connected graph has a nice ear-decomposition. -/
theorem lemma_10 (G : Graph V E) (hG : G.IsTwoVertexConnected) :
    ∃ D : EarDecomposition G, D.IsNice := by sorry

end NicerEars.TJoin
