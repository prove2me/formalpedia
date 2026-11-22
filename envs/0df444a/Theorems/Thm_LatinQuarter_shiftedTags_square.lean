-- Prove2me | Theorems.Thm_LatinQuarter_shiftedTags_square
-- name    : LatinQuarter.shiftedTags_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:20.112003+00:00
-- url     : https://prove2.me/theorems/8da26443-8110-4f0a-a6df-8a1bc3591a8c
-- title:
--   Latin Quarter: shifted Tags square
-- statement:
--   The Latin Quarter construction uses the shifted Tags square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Shifted.lean#L32-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Shifted.lean#L32-L39

module
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix

theorem LatinQuarter.shiftedTags_square {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) (c s : N) :
    squareHom (shiftedTags e c s) = algebraMap (ZMod 2) _ (markedConstant e c s) := by sorry
