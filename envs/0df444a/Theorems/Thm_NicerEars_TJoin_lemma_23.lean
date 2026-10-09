-- Prove2me | Theorems.Thm_NicerEars_TJoin_lemma_23
-- name    : NicerEars.TJoin.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:41.298195+00:00
-- url     : https://prove2.me/theorems/00d0156d-0c27-4fae-9bf3-8939aa99d770
-- title:
--   Lemma 23 — a nice ear-decomposition containing a maximum earmuff
-- statement:
--   Let $G$ be a 2-vertex-connected graph and $T\subseteq V(G)$ with $|T|$ even. Then $G$ has a nice ear-decomposition containing a maximum earmuff for the eardrum $M$ associated with it and $T$: for some $F\subseteq M$ with $|F|=\mu(G,M)$, the clean ears whose internal vertex sets lie in $F$ form an earmuff.
--
--   This is the ear-decomposition on which Theorem 24 operates.
--
--   **Formalization Note.** The running time $O(|V(G)||E(G)|)$ is not formalized.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 18, Lemma 23

import Mathlib
import Definitions.Def_NicerEars_TJoin_Earmuff

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lemma 23 (p. 18), existence part: a 2-vertex-connected graph `G` and `T ⊆ V(G)` with `|T|` even;
`G` has a nice ear-decomposition containing a maximum earmuff for the eardrum associated with it
and `T`. -/
theorem lemma_23 (G : Graph V E) (hG : G.IsTwoVertexConnected) (T : Finset V) (hT : Even #T) :
    ∃ D : EarDecomposition G, D.IsNice ∧ D.ContainsMaxEarmuff T := by sorry

end NicerEars.TJoin
