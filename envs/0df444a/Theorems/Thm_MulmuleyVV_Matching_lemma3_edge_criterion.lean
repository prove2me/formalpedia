-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_lemma3_edge_criterion
-- name    : MulmuleyVV.Matching.lemma3_edge_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:37:33.704371+00:00
-- url     : https://prove2.me/theorems/45952cca-3bf9-41a8-ba1d-b7c578a410fc
-- title:
--   Lemma 3 — the edge $(v_i, v_j)$ is in the unique minimum weight perfect matching iff $|B_{ij}|2^{w_{ij}}/2^{2w}$ is odd
-- statement:
--   Let $G$, the edge weights $w_{ij} \in \mathbb{N}$ and the matrix $B$ be as in Lemma 2. Let $M$ be the unique minimum weight perfect matching of $G$ and $w$ its weight, and write $|B_{ij}|$ for the determinant of the submatrix of $B$ obtained by deleting row $i$ and column $j$. Then for every edge $(v_i, v_j)$ of $G$,
--
--   $$
--   (v_i, v_j) \in M \iff \frac{|B_{ij}|\, 2^{w_{ij}}}{2^{2w}} \ \text{is odd}.
--   $$
--
--   Together with Lemma 2, this recovers the matching itself from $|B|$ and the minors of $B$, i.e. from the adjugate of $B$.
--
--   **Formalization Note** "$x/2^k$ is odd" is `OddQuot x k`: $2^k \mid x$ and $x/2^k$ is an odd integer. The minor $|B_{ij}|$ is taken as Mathlib's `adjugate B j i`, which equals $(-1)^{i+j}|B_{ij}|$; the sign does not affect the criterion. The statement is for every adjacent ordered pair $(i, j)$, in either order. "Matching" in the printed lemma means perfect matching, as in Lemma 2.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 109, Lemma 3

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

namespace MulmuleyVV.Matching

theorem lemma3_edge_criterion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) (M : Finset G.edgeSet) (hM : IsPerfectMatchingEdges G M)
    (huniq : ∀ M' : Finset G.edgeSet, IsPerfectMatchingEdges G M' → M' ≠ M →
      setWeight w M < setWeight w M')
    (i j : Fin n) (hij : G.Adj i j) :
    (⟨s(i, j), G.mem_edgeSet.mpr hij⟩ : G.edgeSet) ∈ M ↔
      OddQuot ((weightedTutteMatrix G w).adjugate j i *
          (2 : ℤ) ^ w ⟨s(i, j), G.mem_edgeSet.mpr hij⟩)
        (2 * setWeight w M) := by sorry

end MulmuleyVV.Matching
