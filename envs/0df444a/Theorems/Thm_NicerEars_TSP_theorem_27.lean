-- Prove2me | Theorems.Thm_NicerEars_TSP_theorem_27
-- name    : NicerEars.TSP.theorem_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:24.264173+00:00
-- url     : https://prove2.me/theorems/c0bc1b31-e340-4508-b5cf-0f6ccfe44b3d
-- title:
--   Theorem 27 (Mömke–Svensson) — a tour with at most 4/3|E(G)| − 2/3|R| edges
-- statement:
--   **Theorem 27** (Lemma 3.2 of Mömke and Svensson [2011]). Let $G$ be a 2-vertex-connected graph and $(R,\mathcal P)$ a removable pairing of $G$. Then $G$ has a tour of cardinality at most
--
--   $$\tfrac43|E(G)|-\tfrac23|R|.$$
--
--   A tour is a connected $\emptyset$-join in $2G$. The bound turns removable edges into savings over the trivial tour, and is the engine of the second tour construction (Lemma 28) used when there are few pendant ears. Its proof in the paper rests on the odd-join (T-join) polytope of an auxiliary 2-edge-connected graph.
--
--   **Formalization Note.** The theorem is stated as existence of the tour; the $O(|V(G)|^3)$ algorithm is not formalized. "2-vertex-connected" is read as 2-edge-connected with no cut vertex.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 20, Theorem 27 (Lemma 3.2 of Mömke and Svensson [2011])

import Mathlib
import Definitions.Def_NicerEars_TSP_RemovablePairing

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 27 (Lemma 3.2 of Mömke and Svensson [2011]), p. 20: a 2-vertex-connected graph G with
a removable pairing (R, 𝒫) has a tour of cardinality at most 4/3 |E(G)| − 2/3 |R|. -/
theorem theorem_27 (G : Graph V E) (hG : G.IsTwoVertexConnected) (R : Finset E)
    (Pairs : Finset (Finset E)) (hRP : G.IsRemovablePairing R Pairs) :
    ∃ F : Finset (E × Fin 2), G.IsTour F ∧
      (#F : ℝ) ≤ 4 / 3 * (Fintype.card E : ℝ) - 2 / 3 * (#R : ℝ) := by sorry

end NicerEars.TSP
