-- Prove2me | Theorems.Thm_LeanModelChecking_LTL_toNNFCore_sound
-- name    : LeanModelChecking.LTL.toNNFCore_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:06.112743+00:00
-- url     : https://prove2.me/theorems/9a0becc5-dc35-4572-9193-79bfd615d570
-- title:
--   LTL: to NNFCore sound
-- statement:
--   The LTL construction uses the to NNFCore sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean#L91-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean#L91-L126

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LTL

theorem LeanModelChecking.LTL.toNNFCore_sound {AP} (f : LTL AP) :
    (∀ w, LTL.language f w ↔ NNF.language (toNNF f) w) ∧
      (∀ w, ¬ LTL.language f w ↔ NNF.language (toNNFNeg f) w) := by sorry
