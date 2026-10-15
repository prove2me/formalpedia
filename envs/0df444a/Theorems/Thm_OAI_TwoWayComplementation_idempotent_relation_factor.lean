-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_idempotent_relation_factor
-- name    : OAI.TwoWayComplementation.idempotent_relation_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:29:38.384284+00:00
-- url     : https://prove2.me/theorems/1aec059a-c110-41c2-8499-858cd65e5d4d
-- title:
--   In an idempotent relation on a finite set, every pair factors through a point with a loop
-- statement:
--   Let $\alpha$ be a finite set and let $P\subseteq\alpha\times\alpha$ be an idempotent relation, $PP=P$, where $PP=\{(x,z):\ \exists y,\ (x,y)\in P\ \text{and}\ (y,z)\in P\}$ is the composition of $P$ with itself. Then for every pair $(u,v)\in P$ there is a point $p\in\alpha$ such that
--   $$(u,p)\in P,\qquad (p,p)\in P,\qquad (p,v)\in P .$$
--
--   Idempotence says that $P$ is transitive ($PP\subseteq P$) and that every pair of $P$ splits into two pairs of $P$ ($P\subseteq PP$). The theorem says that on a finite set one of the splitting points can be chosen recurrent, that is, with a loop $(p,p)\in P$. Finiteness cannot be dropped: the strict order $<$ on $\mathbb{Q}$ satisfies $PP=P$ but has no loop. Applied to the recurrence relation of an idempotent boundary diagram, the theorem shows that every through-traversal passes a recurrent point, so that the through relation is covered by the rectangles of recurrent points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean#L317-L347

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.idempotent_relation_factor {α : Type*} [Finite α] (P : SetRel α α)
    (hP : P ○ P = P) {u v : α} (huv : (u, v) ∈ P) :
    ∃ p, (u, p) ∈ P ∧ (p, p) ∈ P ∧ (p, v) ∈ P := by sorry
