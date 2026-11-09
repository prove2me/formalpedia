-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_weighted_proximity
-- name    : GroupLabeledMatroid.Proximity.weighted_proximity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:00.068624+00:00
-- url     : https://prove2.me/theorems/6e030a41-8ae5-4e3d-b9d6-e235901afc6d
-- title:
--   Theorem 1 — sharp weighted proximity for forbidden-label bases
-- statement:
--   Let $M$ be any finite matroid, $G$ any abelian group, $F\subseteq G$ a finite forbidden set, and $\ell:E\to G$, $c:E\to\mathbb R$ arbitrary label and cost maps. For every minimum-cost base $A$, if any $F$-avoiding base exists, there is a base $B$ of minimum cost among all $F$-avoiding bases such that
--
--   $$d(A,B)=|A\setminus B|\le |F|.$$
--
--   This is the full weighted proximity theorem. It allows infinite label groups, negative costs, tied optima, empty ground, rank zero, and empty forbidden sets. The optimum $B$ is global within the avoiding family; existence of a nearby avoiding base or a nearby optimum is not a hypothesis.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 2, Theorem 1 (Proximity); restated p. 10, proof pp. 10–11

import Definitions.Def_GroupLabeledMatroid_Proximity_LabelModel

namespace GroupLabeledMatroid.Proximity

theorem weighted_proximity {E G : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup G] [DecidableEq G] (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (F : Finset G) (A : Finset E) (hA : IsMinimumBase M c A)
    (hex : ∃ D : Finset E, IsAvoidingBase M ℓ F D) :
    ∃ B : Finset E, IsMinimumAvoidingBase M ℓ c F B ∧ baseDistance A B ≤ F.card := by sorry

end GroupLabeledMatroid.Proximity
