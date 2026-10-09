-- Prove2me | Theorems.Thm_NicerEars_TJoin_theorem_24
-- name    : NicerEars.TJoin.theorem_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:42.555737+00:00
-- url     : https://prove2.me/theorems/f34b5441-1b90-4f5a-bbc7-570591a55017
-- title:
--   Theorem 24 — a connected-T-join with at most L_µ(G,M) + ½L_ϕ(G) − π edges
-- statement:
--   Let $G$ be a graph and $T\subseteq V(G)$ with $|T|$ even, given with a nice ear-decomposition of $G$ containing a maximum earmuff for the eardrum $M$ associated with it and $T$. Then there is a connected-$T$-join of $G$ of cardinality at most
--   $$L_\mu(G,M)+\tfrac12L_\varphi(G)-\pi,$$
--   where $L_\mu(G,M)=|V(G)|-1+|M|-\mu(G,M)$, $L_\varphi(G)=|V(G)|+\varphi(G)-1$, and $\pi$ is the number of pendant ears.
--
--   This is the construction used, for all three problems of the paper, when there are many pendant ears.
--
--   **Formalization Note.** The algorithm and its running time $O(|V(G)|^3)$ are not formalized; the statement asserts existence. 2-edge-connectivity of $G$ is not a hypothesis: it is implied by the existence of the ear-decomposition.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 18, Theorem 24

import Mathlib
import Definitions.Def_NicerEars_TJoin_Earmuff

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 24 (p. 18), existence part: given `T ⊆ V(G)` with `|T|` even and a nice
ear-decomposition of `G` containing a maximum earmuff for the eardrum `M` associated with it and
`T`, there is a connected-T-join of cardinality at most `L_µ(G, M) + ½L_ϕ(G) − π`, where `π` is the
number of pendant ears. -/
theorem theorem_24 (G : Graph V E) (T : Finset V) (hT : Even #T) (D : EarDecomposition G)
    (hnice : D.IsNice) (hmax : D.ContainsMaxEarmuff T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      (#F : ℝ) ≤ Lmu G (D.eardrumOf T) + 1 / 2 * Lphi G - D.numPendant := by sorry

end NicerEars.TJoin
