-- Prove2me | Theorems.Thm_NashWilliams_reach_uncov_reachable
-- name    : NashWilliams.reach_uncov_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:45:36.694416+00:00
-- url     : https://prove2.me/theorems/55ebcf42-5fb3-485b-9c9c-a5e82dba9ab6
-- title:
--   Nash Williams: reach uncov reachable
-- statement:
--   The Nash Williams construction uses the reach uncov reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L336-L353
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L336-L353

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

theorem NashWilliams.reach_uncov_reachable {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (Step G) F₀ F) {u v : V} (huv : Uncov G F u v) (i : Fin k) :
    (F i ⊓ exchGraph G F₀).Reachable u v := by sorry
