-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_f3t_self_add_ne_zero
-- name    : InverseZeroSum.Candidate3.f3t_self_add_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:08.695616+00:00
-- url     : https://prove2.me/theorems/f68f8f71-a8d5-44fd-aa0c-a4d3856d967d
-- title:
--   Candidate3: f3t self add ne zero
-- statement:
--   The Candidate3 construction uses the f3t self add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1477-L1479
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1477-L1479

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.f3t_self_add_ne_zero :
    ∀ x : F3T, x ≠ 0 → x + x ≠ 0 := by sorry
