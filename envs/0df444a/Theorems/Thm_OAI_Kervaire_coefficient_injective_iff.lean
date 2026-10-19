-- Prove2me | Theorems.Thm_OAI_Kervaire_coefficient_injective_iff
-- name    : OAI.Kervaire.coefficient_injective_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:23:58.110987+00:00
-- url     : https://prove2.me/theorems/967b8097-c006-456c-ace4-bcc866c2aeab
-- title:
--   Injectivity of the coefficient map via the normal closure
-- statement:
--   Let $A$ be a group, $w\in A*\langle t\rangle$, and let $\iota:A\to(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ be the natural map. Then $\iota$ is injective if and only if
--   $$
--   a\in\langle\!\langle w\rangle\!\rangle\ \Longrightarrow\ a=1\qquad(a\in A),
--   $$
--   where $A$ is viewed inside the free product.
--
--   So injectivity reduces to showing that no nontrivial coefficient lies in the normal closure of the relator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Reductions.lean#L9-L24

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions

open OAI OAI.Kervaire
universe u

theorem OAI.Kervaire.coefficient_injective_iff {A : Type u} [Group A] (w : WordGroup A) :
    Function.Injective (coefficientMap w) ↔
      ∀ a : A, Monoid.Coprod.inl a ∈ relatorClosure w → a = 1 := by sorry
