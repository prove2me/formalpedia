-- Prove2me | Theorems.Thm_OAI_Release075_relationGraph_cycle_encoding
-- name    : OAI.Release075.relationGraph_cycle_encoding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:42:46.156335+00:00
-- url     : https://prove2.me/theorems/caebf681-e514-47fa-b7bc-45e5f45aa588
-- title:
--   Normal form of a cycle in a bipartite relation graph
-- statement:
--   Let $R\subseteq A\times B$ be a relation and consider the simple bipartite graph on $A\sqcup B$ whose edges are the pairs related by $R$. Every cycle starting at a vertex $a\in A$ has even length $2s$ with $s\ge2$. Moreover there are injective sequences $p:\mathbb Z/s\to A$ and $l:\mathbb Z/s\to B$ with
--   $$
--   R\bigl(p_i,l_i\bigr)\quad\text{and}\quad R\bigl(p_{i+1},l_i\bigr)\qquad\text{for all }i\in\mathbb Z/s .
--   $$
--
--   So the cycle alternates $p_0,l_0,p_1,l_1,\dots$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L397-L444

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.Release075.relationGraph_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A} (w : (relationGraph R).Walk (.inl a) (.inl a)) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by sorry
