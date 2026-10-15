-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_feedback_lost_edge
-- name    : OAI.TwoWayComplementation.feedback_lost_edge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:27:52.496977+00:00
-- url     : https://prove2.me/theorems/4c7f4641-c49a-41e2-a6dc-35fd80f8d3e7
-- title:
--   A lost alternating traversal passes through a lost edge
-- statement:
--   Let $\alpha$ be a set and let $E$, $E'$ and $B$ be relations on $\alpha$. Relations compose in path order, $(x,z)\in RS\iff\exists y:\ (x,y)\in R\ \text{and}\ (y,z)\in S$, and $R^*$ denotes the reflexive–transitive closure. Let $x,y\in\alpha$ and suppose that
--   $$(x,y)\in E\,(BE)^*\qquad\text{but}\qquad (x,y)\notin E'\,(BE')^* .$$
--   Then there are $a,b\in\alpha$ such that
--   $$(x,a)\in(EB)^*,\qquad (a,b)\in E,\qquad (a,b)\notin E',\qquad (b,y)\in(BE)^* .$$
--
--   Think of $E$ as traversal edges and of $B$ as bounce edges: $E(BE)^*$ consists of the walks that alternate between traversals and bounces and begin and end with a traversal. If such a walk from $x$ to $y$ exists for $E$ but none exists for $E'$, then some alternating walk from $x$ to $y$ uses a traversal edge $(a,b)$ of $E$ that is not an edge of $E'$, possibly after earlier and before later bounces. No relation between $E$ and $E'$ is assumed. In the lower-bound argument, $E$ and $E'$ are the port relations of an idempotent boundary diagram and of a replacement for it, and $B$ is the bounce relation of a surrounding context: a feedback traversal that is lost under the replacement must use a port edge that the replacement lacks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean#L234-L251

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.feedback_lost_edge {α : Type*} (E E' B : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ E ○ relStar (B ○ E))
    (hnot : (x, y) ∉ E' ○ relStar (B ○ E')) :
    ∃ a b, (x, a) ∈ relStar (E ○ B) ∧ (a, b) ∈ E ∧
      (a, b) ∉ E' ∧ (b, y) ∈ relStar (B ○ E) := by sorry
