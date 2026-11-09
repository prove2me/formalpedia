-- Prove2me | Theorems.Thm_GapCliqueLB_Clique_proposition_5_5
-- name    : GapCliqueLB.Clique.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:49:37.087595+00:00
-- url     : https://prove2.me/theorems/efb4c618-1a3d-45bd-9114-e49b1b59af64
-- title:
--   Proposition 5.5 — pairwise covering disperser from an exact pair cover
-- statement:
--   Let $h\ge5$ and let $B$ be any family of two- and three-element subsets of $[h]$ in which every pair occurs in exactly one block. Put $b=|B|$ and $T_i=\{A\in B:i\notin A\}$. Then
--
--   $$T\text{ is a pairwise }(b,h,3,3)\text{-covering disperser},\qquad |T_i\cup T_j|=b-1\quad(i\ne j).$$
--
--   The disperser conclusion includes properness of every $T_i$ and the inequalities $2\le3<b$ and $1\le3<h$; none is an additional hypothesis. A bijection indexes the universe $B$ by $[b]$. The cover need not minimize its number of blocks. This supplies the set system for the Clique reduction.
--
--   Differences from the source:
--   - encoding: finite sets [k] and [ℓ] with their named elements → Fin k and Fin ℓ, with bijective indexing of the blocks B in Proposition 5.5; reason: zero-based indexing changes no finite instance
-- source:
--   Reina Itakura, Karthik C.S., Mayank Motwani, Gary Peng, STOC 2027 submission #232 (October 2026), Proposition 5.5, PDF p. 20 (printed p. 19), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/232.pdf

import Definitions.Def_GapCliqueLB_Clique_Dispersers

namespace GapCliqueLB.Clique

/-- Proposition 5.5, PDF p. 20. The universe B is indexed bijectively by Fin B.card. -/
theorem proposition_5_5 (h : ℕ) (hh : 5 ≤ h)
    (B : Finset (Finset (Fin h))) (hB : B ∈ PairCover h) :
    PairwiseCoveringDisperser (indexedPartitionSets B) 3 3 ∧
      ∀ i j : Fin h, i ≠ j →
        (partitionSets B i ∪ partitionSets B j).card = B.card - 1 := by sorry

end GapCliqueLB.Clique
