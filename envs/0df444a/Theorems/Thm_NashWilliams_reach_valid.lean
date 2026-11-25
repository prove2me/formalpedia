-- Prove2me | Theorems.Thm_NashWilliams_reach_valid
-- name    : NashWilliams.reach_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:41:44.138812+00:00
-- url     : https://prove2.me/theorems/61980df7-a5f1-43a7-94fd-c36e19f362b5
-- title:
--   Nash Williams: reach valid
-- statement:
--   The Nash Williams construction uses the reach valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L330-L334
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L330-L334

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
omit hmax

theorem NashWilliams.reach_valid {F : Fin k → SimpleGraph V} (hF : Relation.ReflTransGen (Step G) F₀ F) :
    Valid G F ∧ total F = total F₀ := by sorry
