-- Prove2me | Theorems.Thm_NicerEars_TSP_lemma_28
-- name    : NicerEars.TSP.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:33.762001+00:00
-- url     : https://prove2.me/theorems/e9548cac-f402-4c8c-b185-90f19a7e9221
-- title:
--   Lemma 28 — a tour with at most 4/3(|V(G)| − 1) + 2/3π edges when all ears are nontrivial
-- statement:
--   **Lemma 28.** Let $G$ be a 2-vertex-connected graph with an ear-decomposition in which all ears are nontrivial. Then $G$ has a tour of cardinality at most
--
--   $$\tfrac43\big(|V(G)|-1\big)+\tfrac23\pi,$$
--
--   where $\pi$ is the number of pendant ears.
--
--   This is the second tour construction of the 7/5 analysis: it is good when there are few pendant ears.
--
--   **Formalization Note.** Stated as existence of the tour; the $O(|V(G)|^3)$ time bound is not formalized. "All ears nontrivial" means every ear has length at least 2. "2-vertex-connected" is read as 2-edge-connected with no cut vertex.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 21, Lemma 28

import Mathlib
import Definitions.Def_NicerEars_TSP_Ears

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lemma 28, p. 21: a 2-vertex-connected graph G with an ear-decomposition in which all ears are
nontrivial has a tour of cardinality at most 4/3 (|V(G)| − 1) + 2/3 π, where π is the number of
pendant ears. -/
theorem lemma_28 (G : Graph V E) (hG : G.IsTwoVertexConnected) (D : EarDecomposition G)
    (hD : ∀ i, (D.ear i).IsNontrivial) :
    ∃ F : Finset (E × Fin 2), G.IsTour F ∧
      (#F : ℝ) ≤ 4 / 3 * ((Fintype.card V : ℝ) - 1) + 2 / 3 * (D.numPendant : ℝ) := by sorry

end NicerEars.TSP
