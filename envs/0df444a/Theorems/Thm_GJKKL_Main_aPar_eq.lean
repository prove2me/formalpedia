-- Prove2me | Theorems.Thm_GJKKL_Main_aPar_eq
-- name    : GJKKL.Main.aPar_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:57.848806+00:00
-- url     : https://prove2.me/theorems/3babd667-f2d0-42b9-bb7d-20695f02c367
-- title:
--   Main: a Par eq
-- statement:
--   The Main construction uses the a Par eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Theorem.lean#L50-L54
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Theorem.lean#L50-L54

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
public import Definitions.Def_GJKKL_Main_Theorem
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics

theorem GJKKL.Main.aPar_eq {V : Type*} [Fintype V] {k : ℕ} (hk0 : (k : ℝ) ≠ 0)
    (hn0 : (Fintype.card V : ℝ) ≠ 0) (t : ℕ) :
    aPar V k t = (Fintype.card V : ℝ) / k * pfrac ((Fintype.card V : ℝ) / k) t := by sorry
