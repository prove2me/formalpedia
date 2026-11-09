-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_block_label_count
-- name    : GroupLabeledMatroid.Proximity.block_label_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:15.420199+00:00
-- url     : https://prove2.me/theorems/4e896c71-330f-43ba-8f04-e27a2fe0244d
-- title:
--   Theorem 18 — block-matroid label count
-- statement:
--   Let $M$ have positive rank and ground $E=A\mathbin{\dot\cup}B$, where $A$ is a minimum-cost base and $B$ is the unique minimum-cost base in its label fiber. Costs are arbitrary reals, labels lie in an arbitrary abelian group, and equal element costs are allowed. Write $r$ for the rank of $M$. The bases whose cost is at most $c(B)$ have at least $r+1$ distinct label sums:
--
--   $$|\ell_{\le c(B)}(M)|\ge r+1.$$
--
--   The threshold family contains all qualifying bases, and the constant is exactly one. This is the block counting theorem used in the proximity theorem.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 9, Theorem 18; proof p. 10; §3 p. 6 and §3.2 p. 8 standing hypotheses

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem block_label_count {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (A B : Finset E)
    (hblock : IsBlockPair M ℓ c A B) (hpos : 0 < M.eRank.toNat) :
    (labelsUnder M ℓ c (costSum c B)).card ≥ M.eRank.toNat + 1 := by sorry

end GroupLabeledMatroid.Proximity
