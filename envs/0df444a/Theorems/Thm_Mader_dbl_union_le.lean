-- Prove2me | Theorems.Thm_Mader_dbl_union_le
-- name    : Mader.dbl_union_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:32.023993+00:00
-- url     : https://prove2.me/theorems/e38d3e3b-2943-4d7d-878e-a4fd2875a677
-- title:
--   Mader: dbl union le
-- statement:
--   The Mader construction uses the dbl union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L96-L107
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L96-L107

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)

theorem Mader.dbl_union_le {S H₁ H₂ : Finset V}
    (hcov : ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → (a ∈ H₁ ∧ b ∈ H₁) ∨ (a ∈ H₂ ∧ b ∈ H₂)) :
    dbl G S ≤ dbl G H₁ + dbl G H₂ := by sorry
