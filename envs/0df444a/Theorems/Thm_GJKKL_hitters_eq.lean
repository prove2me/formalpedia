-- Prove2me | Theorems.Thm_GJKKL_hitters_eq
-- name    : GJKKL.hitters_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:18.393016+00:00
-- url     : https://prove2.me/theorems/aef64f2d-b03d-43ca-bbfe-8d9e22995956
-- title:
--   GJKKL: hitters eq
-- statement:
--   The GJKKL construction uses the hitters eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L68-L79
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L68-L79

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.hitters_eq {H : Finset (Finset V)} {h : List (Finset V)} {v : V} {f : Finset V} :
    hitters H h v f =
      (f.erase v).biUnion (fun u => (avail H h \ Dv H h v).filter (fun a => u ∈ a)) := by sorry
