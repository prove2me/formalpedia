-- Prove2me | Theorems.Thm_GJKKL_disjoint_of_pairwise
-- name    : GJKKL.disjoint_of_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:20.053146+00:00
-- url     : https://prove2.me/theorems/a71d78d2-f4e2-4f69-a44f-81e9d312fa8a
-- title:
--   GJKKL: disjoint of pairwise
-- statement:
--   The GJKKL construction uses the disjoint of pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L211-L222
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L211-L222

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem GJKKL.disjoint_of_pairwise : ∀ {h : List (Finset V)}, h.Pairwise Disjoint →
    ∀ {e f : Finset V}, e ∈ h → f ∈ h → e ≠ f → Disjoint e f
  := by sorry
