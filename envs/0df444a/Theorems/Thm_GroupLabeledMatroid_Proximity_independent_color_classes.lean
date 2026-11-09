-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_independent_color_classes
-- name    : GroupLabeledMatroid.Proximity.independent_color_classes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:50.092451+00:00
-- url     : https://prove2.me/theorems/62f16d9d-c4c0-47e8-9ed0-a0f39c890bbb
-- title:
--   Lemma 15 — independent color classes
-- statement:
--   Let $M$ have positive rank and ground $E=A\mathbin{\dot\cup}B$, where $A$ is a minimum-cost base and $B$ is the unique minimum-cost base in its label fiber. Costs are arbitrary reals, labels lie in an arbitrary abelian group, and equal element costs are allowed. Every individual color class is independent:
--
--   $$E_h=\{e\in E:\ell(e)=h\}\in\mathcal I\qquad(h\in G).$$
--
--   This result uses the block and optimality assumptions; it makes no assertion for an arbitrary colored matroid without those hypotheses.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 9, Lemma 15; §3 p. 6 and §3.2 p. 8 standing hypotheses

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem independent_color_classes {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (A B : Finset E)
    (hblock : IsBlockPair M ℓ c A B) (hpos : 0 < M.eRank.toNat) (h : G) :
    M.Indep (colorClass M ℓ h : Set E) := by sorry

end GroupLabeledMatroid.Proximity
