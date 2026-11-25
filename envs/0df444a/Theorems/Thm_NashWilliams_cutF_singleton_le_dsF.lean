-- Prove2me | Theorems.Thm_NashWilliams_cutF_singleton_le_dsF
-- name    : NashWilliams.cutF_singleton_le_dsF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:04:34.512473+00:00
-- url     : https://prove2.me/theorems/e21042fb-235e-541e-bdc5-6ade27ae2037
-- title:
--   Nash Williams: cut F singleton le ds F
-- statement:
--   The Nash Williams construction uses the cut F singleton le ds F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L155-L171
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L155-L171

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_singleton_le_dsF {s : V} {ends : ι → V × V} {F : Finset ι} {X : Finset V}
    (h : ∀ l ∈ F, ((ends l).1 = s) ≠ ((ends l).2 = s) → oth s (ends l) ∈ X) :
    cutF ends F {s} ≤ dsF s ends F X := by sorry
