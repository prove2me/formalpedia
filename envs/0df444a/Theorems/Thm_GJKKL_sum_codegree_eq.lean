-- Prove2me | Theorems.Thm_GJKKL_sum_codegree_eq
-- name    : GJKKL.sum_codegree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:24.603051+00:00
-- url     : https://prove2.me/theorems/19454d0a-4e6f-4cb6-8c10-97cb1d47e961
-- title:
--   GJKKL: sum codegree eq
-- statement:
--   The GJKKL construction uses the sum codegree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/VertexCount.lean#L26-L39
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/VertexCount.lean#L26-L39

module
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_VertexCount
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.sum_codegree_eq (H : Finset (Finset V)) (v : V) :
    ∑ u ∈ univ.erase v, codegree H v u = ∑ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card := by sorry
