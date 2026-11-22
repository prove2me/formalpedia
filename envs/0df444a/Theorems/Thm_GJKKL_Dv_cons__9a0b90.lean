-- Prove2me | Theorems.Thm_GJKKL_Dv_cons__9a0b90
-- name    : GJKKL.Dv_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:35.148802+00:00
-- url     : https://prove2.me/theorems/9a0b9059-71bb-4fb8-9c12-c344e4223088
-- title:
--   GJKKL: Dv cons
-- statement:
--   The GJKKL construction uses the Dv cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L50-L54
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L50-L54

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.Dv_cons (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) (v : V) :
    Dv H (a :: h) v = (Dv H h v).filter (fun e => Disjoint e a) := by sorry
