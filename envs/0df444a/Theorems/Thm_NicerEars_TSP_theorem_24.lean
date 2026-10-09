-- Prove2me | Theorems.Thm_NicerEars_TSP_theorem_24
-- name    : NicerEars.TSP.theorem_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:43.394102+00:00
-- url     : https://prove2.me/theorems/4c120a4d-a9d9-4be1-8953-b180200e6baa
-- title:
--   Theorem 24 — a connected-T-join with at most L_µ(G, M) + ½L_ϕ(G) − π edges
-- statement:
--   **Theorem 24.** Let $G$ be a graph and $T\subseteq V(G)$ with $|T|$ even, given with a nice ear-decomposition of $G$ containing a maximum earmuff for the eardrum $M$ associated with it and $T$. Then $G$ has a connected-$T$-join of cardinality at most
--
--   $$L_\mu(G,M)+\tfrac12L_\varphi(G)-\pi,$$
--
--   where $\pi$ is the number of pendant ears.
--
--   For $T=\emptyset$ this is the first of the two tour constructions of the 7/5 analysis: it is good when there are many pendant ears.
--
--   **Formalization Note.** The theorem is stated as the existence of the connected-$T$-join; the $O(|V(G)|^3)$ construction time is not formalized. The given ear-decomposition makes $G$ 2-edge-connected, so no connectivity hypothesis is needed.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 18, Theorem 24

import Mathlib
import Definitions.Def_NicerEars_TSP_Earmuff

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 24, p. 18: given a nice ear-decomposition of G containing a maximum earmuff for the
eardrum M associated with it and T (|T| even), there is a connected-T-join of cardinality at most
L_µ(G, M) + ½ L_ϕ(G) − π, where π is the number of pendant ears. -/
theorem theorem_24 (G : Graph V E) (T : Finset V) (hT : Even #T) (D : EarDecomposition G)
    (hnice : D.IsNice) (hmax : D.ContainsMaxEarmuff T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      (#F : ℝ) ≤ (G.Lmu (D.eardrumOf T) : ℝ) + 1 / 2 * (G.Lphi : ℝ) - D.numPendant := by sorry

end NicerEars.TSP
