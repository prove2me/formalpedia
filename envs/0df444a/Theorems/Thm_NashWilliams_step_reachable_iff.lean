-- Prove2me | Theorems.Thm_NashWilliams_step_reachable_iff
-- name    : NashWilliams.step_reachable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:55:37.707602+00:00
-- url     : https://prove2.me/theorems/7a50f91a-6f4a-508f-870f-28a035902a6c
-- title:
--   Nash Williams: step reachable iff
-- statement:
--   The Nash Williams construction uses the step reachable iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L355-L383
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L355-L383

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

theorem NashWilliams.step_reachable_iff {F F' : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (Step G) F₀ F) (hstep : Step G F F') (j : Fin k) (a b : V) :
    (F j ⊓ exchGraph G F₀).Reachable a b ↔ (F' j ⊓ exchGraph G F₀).Reachable a b := by sorry
