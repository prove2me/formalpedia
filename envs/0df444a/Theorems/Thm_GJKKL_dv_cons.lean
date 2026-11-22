-- Prove2me | Theorems.Thm_GJKKL_dv_cons
-- name    : GJKKL.dv_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:07.546412+00:00
-- url     : https://prove2.me/theorems/d656c6e8-89c2-4847-b499-5d1eadcf0f77
-- title:
--   GJKKL: dv cons
-- statement:
--   The one-step change of the remaining degree.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L57-L60
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L57-L60

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.dv_cons (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) (v : V) :
    dv H (a :: h) v + ((Dv H h v).filter (fun e => ¬ Disjoint e a)).card = dv H h v := by sorry
