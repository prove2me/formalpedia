-- Prove2me | Theorems.Thm_OAI_Release075_relationGraph_any_cycle_encoding
-- name    : OAI.Release075.relationGraph_any_cycle_encoding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:43:16.296691+00:00
-- url     : https://prove2.me/theorems/279de886-4220-44d7-b2e2-36f836b702a8
-- title:
--   Cycle normal form from any starting vertex
-- statement:
--   Let $R\subseteq A\times B$ be a relation and consider the simple bipartite graph on $A\sqcup B$ whose edges are the pairs related by $R$. Every cycle, starting at any vertex, has length $2s$ with $s\ge2$, and there are injective $p:\mathbb Z/s\to A$ and $l:\mathbb Z/s\to B$ with
--   $$
--   R(p_i,l_i)\quad\text{and}\quad R(p_{i+1},l_i)\qquad(i\in\mathbb Z/s).
--   $$
--
--   This removes the restriction that the cycle starts on the $A$ side.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L446-L463

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.Release075.relationGraph_any_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A ⊕ B} (w : (relationGraph R).Walk a a) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by sorry
