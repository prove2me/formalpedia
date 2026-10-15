-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_blockRelation_star_right
-- name    : OAI.TwoWayComplementation.blockRelation_star_right
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:26:14.737564+00:00
-- url     : https://prove2.me/theorems/0f214a32-88b2-464d-9b95-7245e050568e
-- title:
--   Paths inside one block of a two-block graph: each excursion into the other block becomes a single edge
-- statement:
--   Let $\alpha$ and $\beta$ be sets and let $E\subseteq\alpha\times\alpha$, $F\subseteq\alpha\times\beta$, $G\subseteq\beta\times\alpha$ and $H\subseteq\beta\times\beta$ be relations. Write $\iota_\alpha$ and $\iota_\beta$ for the embeddings of $\alpha$ and $\beta$ into the disjoint union $\alpha\sqcup\beta$, and let $\mathcal B$ be the block relation $\begin{bmatrix}E&F\\G&H\end{bmatrix}$ on $\alpha\sqcup\beta$: it relates $\iota_\alpha(a)$ to $\iota_\alpha(b)$ iff $(a,b)\in E$, $\iota_\alpha(a)$ to $\iota_\beta(b)$ iff $(a,b)\in F$, $\iota_\beta(a)$ to $\iota_\alpha(b)$ iff $(a,b)\in G$, and $\iota_\beta(a)$ to $\iota_\beta(b)$ iff $(a,b)\in H$. Relations compose in path order, $(x,z)\in RS\iff\exists y:\ (x,y)\in R\ \text{and}\ (y,z)\in S$, and $R^*$ denotes the reflexive–transitive closure. Then for all $x,y\in\beta$,
--   $$\big(\iota_\beta(x),\iota_\beta(y)\big)\in\mathcal B^*\iff (x,y)\in\big(H\cup G\,E^*F\big)^* .$$
--
--   In words, a path in the two-block graph between two vertices of the $\beta$-block consists of $H$-edges and of excursions into the $\alpha$-block, each of which enters by a $G$-edge, moves inside $\alpha$ along $E$ and returns by an $F$-edge; replacing every excursion by one edge of $GE^*F$ gives a path inside $\beta$, and conversely. This is the elimination of one block of vertices from a partitioned graph. It is used to compute the summary of two joined networks, whose edge relation is a block relation of this form.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean#L41-L75

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.blockRelation_star_right {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : β) :
    ((Sum.inr x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar (H ∪ (G ○ relStar E ○ F)) := by sorry
