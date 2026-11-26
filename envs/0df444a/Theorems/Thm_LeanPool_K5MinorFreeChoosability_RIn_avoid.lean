-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_avoid
-- name    : LeanPool.K5MinorFreeChoosability.RIn.avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:27.736153+00:00
-- url     : https://prove2.me/theorems/c05bc4d3-a489-4909-a8f3-704d72eee5dc
-- title:
--   RIn: avoid
-- statement:
--   A walk from `a` that never meets the reachability class of a forbidden vertex avoids it:
--   if `t` is not reachable from `a` inside `s`, then reachability inside `s` agrees with
--   reachability inside `s \ {t}` for walks starting at `a`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L113-L119
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L113-L119

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}

theorem LeanPool.K5MinorFreeChoosability.RIn.avoid (h : RIn G s a b) {t : W} (ht : ¬ RIn G s a t) : RIn G (s \ {t}) a b := by sorry
