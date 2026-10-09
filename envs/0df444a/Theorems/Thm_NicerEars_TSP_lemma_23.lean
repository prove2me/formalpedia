-- Prove2me | Theorems.Thm_NicerEars_TSP_lemma_23
-- name    : NicerEars.TSP.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:32.916993+00:00
-- url     : https://prove2.me/theorems/bec4e24e-9d14-4219-89d8-3a124b6260e5
-- title:
--   Lemma 23 — a nice ear-decomposition containing a maximum earmuff exists
-- statement:
--   **Lemma 23.** Let $G$ be a 2-vertex-connected graph and $T\subseteq V(G)$ with $|T|$ even. Then $G$ has a nice ear-decomposition containing a maximum earmuff for the eardrum associated with it and $T$.
--
--   That is, there is an ear-decomposition with $\varphi(G)$ even ears, all short ears pendant and internal vertices of different short ears non-adjacent, such that for the eardrum $M$ formed by the internal vertex sets of its clean ears, the clean ears with internal sets in some $F\subseteq M$, $|F|=\mu(G,M)$, form an earmuff.
--
--   All three approximation algorithms of the paper start from such an ear-decomposition; for the graphic TSP it is used with $T=\emptyset$.
--
--   **Formalization Note.** The running time $O(|V(G)||E(G)|)$ is not formalized; the lemma is stated as existence. "2-vertex-connected" is read as 2-edge-connected with no cut vertex, which includes the one-vertex graph and two vertices joined by parallel edges.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 18, Lemma 23

import Mathlib
import Definitions.Def_NicerEars_TSP_Earmuff

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lemma 23, p. 18: a 2-vertex-connected graph G and T ⊆ V(G) with |T| even: G has a nice
ear-decomposition containing a maximum earmuff for the eardrum associated with it and T. -/
theorem lemma_23 (G : Graph V E) (hG : G.IsTwoVertexConnected) (T : Finset V) (hT : Even #T) :
    ∃ D : EarDecomposition G, D.IsNice ∧ D.ContainsMaxEarmuff T := by sorry

end NicerEars.TSP
