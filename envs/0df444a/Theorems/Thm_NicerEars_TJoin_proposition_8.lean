-- Prove2me | Theorems.Thm_NicerEars_TJoin_proposition_8
-- name    : NicerEars.TJoin.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:59.440007+00:00
-- url     : https://prove2.me/theorems/b5a91a84-d770-492b-a55a-b6d4e99790b5
-- title:
--   Proposition 8 — a connected-T-join with at most 3/2(|V(G)|−1) + π₂ − ½ϕ(G) edges
-- statement:
--   Let $G$ be a 2-edge-connected graph with an ear-decomposition that has $\varphi(G)$ even ears, among which there are $\pi_2$ 2-ears. Then for every $T\subseteq V(G)$ with $|T|$ even there is a connected-$T$-join of $G$ with at most
--   $$\tfrac32\bigl(|V(G)|-1\bigr)+\pi_2-\tfrac12\varphi(G)$$
--   edges.
--
--   This is the construction used in the proof of Theorem 25 when there are few pendant ears.
--
--   **Formalization Note.** The algorithm and its running time $O(|E(G)|)$ are not formalized; the statement asserts existence for every even $T$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 8, Proposition 8

import Mathlib
import Definitions.Def_NicerEars_TJoin_Ears

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proposition 8 (p. 8), existence part: for a 2-edge-connected graph `G` with an
ear-decomposition with ϕ(G) even ears, among which there are π₂ 2-ears, and every `T ⊆ V(G)` with
`|T|` even, there is a connected-T-join with at most `3/2(|V(G)| − 1) + π₂ − ½ϕ(G)` edges. -/
theorem proposition_8 (G : Graph V E) (hG : G.IsTwoEdgeConnected) (D : EarDecomposition G)
    (hD : D.numEven = phi G) (T : Finset V) (hT : Even #T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      (#F : ℝ) ≤ 3 / 2 * ((Fintype.card V : ℝ) - 1) + D.num2Ears - 1 / 2 * phi G := by sorry

end NicerEars.TJoin
