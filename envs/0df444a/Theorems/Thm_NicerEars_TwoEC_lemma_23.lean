-- Prove2me | Theorems.Thm_NicerEars_TwoEC_lemma_23
-- name    : NicerEars.TwoEC.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:56.841128+00:00
-- url     : https://prove2.me/theorems/3fc86ebd-07f0-4ff0-a953-35ce472127cb
-- title:
--   Lemma 23 — a 2-vertex-connected graph has a nice ear-decomposition containing a maximum earmuff
-- statement:
--   Let $G$ be a 2-vertex-connected graph and $T\subseteq V(G)$ with $|T|$ even. Then $G$ has a nice ear-decomposition (Definition 9) that contains a maximum earmuff for the eardrum $M$ associated with it and $T$: for some $F\subseteq M$ with $|F|=\mu(G,M)$, the clean ears whose internal vertex sets belong to $F$ form an earmuff.
--
--   All three approximation algorithms of the paper start from such a decomposition.
--
--   **Formalization Note** The running time $O(|V(G)||E(G)|)$ is not formalized; the lemma states existence. "2-vertex-connected" means 2-edge-connected with no cut vertex; this includes the one-vertex graph and two vertices joined by parallel edges.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 18, Lemma 23

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

namespace NicerEars.TwoEC

open Finset

theorem lemma_23 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsTwoVertexConnected) (T : Finset V) (hT : Even #T) :
    ∃ D : EarDecomposition G, D.IsNice ∧ D.ContainsMaxEarmuff T := by sorry

end NicerEars.TwoEC
