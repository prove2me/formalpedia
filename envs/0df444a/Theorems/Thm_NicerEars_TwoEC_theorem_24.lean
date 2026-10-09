-- Prove2me | Theorems.Thm_NicerEars_TwoEC_theorem_24
-- name    : NicerEars.TwoEC.theorem_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:27.516014+00:00
-- url     : https://prove2.me/theorems/033fc4bb-572a-4b26-a7d3-4ac5f5296442
-- title:
--   Theorem 24 — a connected-T-join with at most L_µ(G,M) + ½L_ϕ(G) − π edges
-- statement:
--   Let $G$ be a graph and $T\subseteq V(G)$ with $|T|$ even, and let a nice ear-decomposition of $G$ be given that contains a maximum earmuff for the eardrum $M$ associated with it and $T$. Let $\pi$ be the number of pendant ears. Then $G$ has a connected-$T$-join $F$ (a $T$-join in $2G$ that connects $V(G)$) with
--
--   $$|F|\le L_\mu(G,M)+\tfrac12L_\varphi(G)-\pi .$$
--
--   For $T=\emptyset$ this is a tour, and it is the construction used when there are many pendant ears.
--
--   **Formalization Note** The algorithm and its $O(|V(G)|^3)$ running time are replaced by existence. The existence of the ear-decomposition makes $G$ 2-edge-connected, so no connectivity hypothesis is added. The bound is compared in the reals.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 18, Theorem 24

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

namespace NicerEars.TwoEC

open Finset

theorem theorem_24 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even #T) (D : EarDecomposition G) (hD : D.IsNice)
    (hmax : D.ContainsMaxEarmuff T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      (#F : ℝ) ≤ (Lmu G (D.eardrumOf T) : ℝ) + 1 / 2 * (Lphi G : ℝ) - D.numPendant := by sorry

end NicerEars.TwoEC
