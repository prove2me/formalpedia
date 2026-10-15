-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_relation_corner_inverse
-- name    : OAI.TwoWayComplementation.relation_corner_inverse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:43:51.135423+00:00
-- url     : https://prove2.me/theorems/f68f0e49-e8e8-4864-a271-7213946d6ef5
-- title:
--   Restriction and extension are inverse between two corners of the relation monoid
-- statement:
--   Let $\alpha$ be a set and consider binary relations on $\alpha$, composed in path order: $XY=\{(x,z):\exists y\ (x,y)\in X,\ (y,z)\in Y\}$. Let $P$ and $i$ be relations on $\alpha$ such that
--   $$
--   P^2=P\qquad\text{and}\qquad iPi=i ,
--   $$
--   and put $Q=PiP$.
--
--   **Theorem.**
--   1. For every relation $Z$ on $\alpha$ with $QZQ=Z$ one has $P\,(iZi)\,P=Z$.
--   2. For every relation $A$ on $\alpha$ with $iAi=A$ one has $Q\,(PAP)\,Q=PAP$ and $i\,(PAP)\,i=A$.
--
--   When $i$ is moreover idempotent, as for the partial identity $\Delta_F=\{(x,x):x\in F\}$ of a subset $F\subseteq\alpha$, this says that restriction $Z\mapsto iZi$ and extension $A\mapsto PAP$ are mutually inverse bijections between the corner $\{Z:QZQ=Z\}$ of the relation monoid at $Q$ and the corner $\{A:iAi=A\}$ at $i$. For $i=\Delta_F$ the second corner consists of the relations contained in $F\times F$; this is how, when $\Delta_FP\Delta_F=\Delta_F$, the corner of the relation monoid at $P\Delta_FP$ is identified with the full relation monoid on $F$.
--
--   **Formalization Note** Relations are `SetRel α α` with path-order composition; $i$ is not assumed to be idempotent, and no finiteness is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean#L41-L69

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.relation_corner_inverse {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    (∀ Z, (P ○ i ○ P) ○ Z ○ (P ○ i ○ P) = Z → P ○ (i ○ Z ○ i) ○ P = Z) ∧
    (∀ A, i ○ A ○ i = A →
      (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) = P ○ A ○ P ∧
      i ○ (P ○ A ○ P) ○ i = A) := by sorry
