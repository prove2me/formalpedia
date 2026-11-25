-- Prove2me | Theorems.Thm_NashWilliams_reach_reachable_iff
-- name    : NashWilliams.reach_reachable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:55:59.903018+00:00
-- url     : https://prove2.me/theorems/b5cec6b2-d82f-40cb-8b7d-1456d2f7909e
-- title:
--   Nash Williams: reach reachable iff
-- statement:
--   The Nash Williams construction uses the reach reachable iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L385-L390
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L385-L390

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable {G : SimpleGraph V} {k : ℕ}
variable [Finite V] {F₀ : Fin k → SimpleGraph V} (hF₀ : Valid G F₀)
  (hmax : ∀ F : Fin k → SimpleGraph V, Valid G F → total F ≤ total F₀)
include hF₀ hmax

theorem NashWilliams.reach_reachable_iff {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (Step G) F₀ F) (j : Fin k) (a b : V) :
    (F j ⊓ exchGraph G F₀).Reachable a b ↔ (F₀ j ⊓ exchGraph G F₀).Reachable a b := by sorry
