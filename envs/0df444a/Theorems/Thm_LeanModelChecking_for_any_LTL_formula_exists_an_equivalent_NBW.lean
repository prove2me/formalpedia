-- Prove2me | Theorems.Thm_LeanModelChecking_for_any_LTL_formula_exists_an_equivalent_NBW
-- name    : LeanModelChecking.for_any_LTL_formula_exists_an_equivalent_NBW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:48.220367+00:00
-- url     : https://prove2.me/theorems/8471986f-3e23-4c2d-bc0c-28cdd2fc4615
-- title:
--   Lean Model Checking: for any LTL formula exists an equivalent NBW
-- statement:
--   The Lean Model Checking construction uses the for any LTL formula exists an equivalent NBW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNBWResult.lean#L35-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNBWResult.lean#L35-L44

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWResult
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking

theorem LeanModelChecking.for_any_LTL_formula_exists_an_equivalent_NBW :
    forAnyLTLFormulaExistsAnEquivalentNBWStatement := by sorry
