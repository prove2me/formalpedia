-- Prove2me | Theorems.Thm_GJKKL_Main_le_rpow_of_root
-- name    : GJKKL.Main.le_rpow_of_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:54.545805+00:00
-- url     : https://prove2.me/theorems/4c545c74-8f65-4c5b-9b51-0f51650ac98f
-- title:
--   Main: le rpow of root
-- statement:
--   The Main construction uses the le rpow of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Theorem.lean#L38-L43
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Theorem.lean#L38-L43

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
public import Definitions.Def_GJKKL_Main_Theorem
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics

theorem GJKKL.Main.le_rpow_of_root {K x d : ℝ} (hK : 0 ≤ K) (hx : 0 < x) (hd : K ^ (1 / x) ≤ d) :
    K ≤ d ^ x := by sorry
