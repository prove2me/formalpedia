-- Prove2me | Theorems.Thm_GJKKL_greedyKernel_K
-- name    : GJKKL.greedyKernel_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:39.160505+00:00
-- url     : https://prove2.me/theorems/60b4085b-e7c1-48c8-a48b-254108b8fca0
-- title:
--   GJKKL: greedy Kernel K
-- statement:
--   The GJKKL construction uses the greedy Kernel K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L130-L131
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L130-L131

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

theorem GJKKL.greedyKernel_K (H : Finset (Finset V)) (h : List (Finset V)) (a : Finset V) :
    (greedyKernel H).K h a = if a ∈ avail H h then ((avail H h).card : ℝ)⁻¹ else 0 := by sorry
