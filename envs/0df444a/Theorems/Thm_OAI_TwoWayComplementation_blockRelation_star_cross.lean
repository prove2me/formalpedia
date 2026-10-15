-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_blockRelation_star_cross
-- name    : OAI.TwoWayComplementation.blockRelation_star_cross
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:27:25.07509+00:00
-- url     : https://prove2.me/theorems/f7b813de-ccf7-4cf1-b3ff-3631868f95ce
-- title:
--   Paths from one block of a two-block graph to the other
-- statement:
--   Let $\alpha$ and $\beta$ be sets and let $E\subseteq\alpha\times\alpha$, $F\subseteq\alpha\times\beta$, $G\subseteq\beta\times\alpha$ and $H\subseteq\beta\times\beta$ be relations. Write $\iota_\alpha$ and $\iota_\beta$ for the embeddings of $\alpha$ and $\beta$ into the disjoint union $\alpha\sqcup\beta$, and let $\mathcal B$ be the block relation $\begin{bmatrix}E&F\\G&H\end{bmatrix}$ on $\alpha\sqcup\beta$: it relates $\iota_\alpha(a)$ to $\iota_\alpha(b)$ iff $(a,b)\in E$, $\iota_\alpha(a)$ to $\iota_\beta(b)$ iff $(a,b)\in F$, $\iota_\beta(a)$ to $\iota_\alpha(b)$ iff $(a,b)\in G$, and $\iota_\beta(a)$ to $\iota_\beta(b)$ iff $(a,b)\in H$. Relations compose in path order, $(x,z)\in RS\iff\exists y:\ (x,y)\in R\ \text{and}\ (y,z)\in S$, and $R^*$ denotes the reflexive–transitive closure. Then for all $x\in\alpha$ and $y\in\beta$,
--   $$\big(\iota_\alpha(x),\iota_\beta(y)\big)\in\mathcal B^*\iff (x,y)\in E^*F\,\big(H\cup G\,E^*F\big)^* .$$
--
--   In words, a path from the $\alpha$-block to the $\beta$-block first moves inside $\alpha$ along $E$, then leaves $\alpha$ for the first time by an $F$-edge, and from then on is a path between vertices of $\beta$, in which every later excursion into $\alpha$ counts as one edge of $GE^*F$. Together with the corresponding description of paths inside the $\beta$-block, this computes the reflexive–transitive closure of a block relation entry by entry; it is used to identify the forward and backward components of the summary of two joined networks with those of the product of their summaries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean#L77-L104

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.blockRelation_star_cross {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x : α) (y : β) :
    ((Sum.inl x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar E ○ F ○ relStar (H ∪ (G ○ relStar E ○ F)) := by sorry
