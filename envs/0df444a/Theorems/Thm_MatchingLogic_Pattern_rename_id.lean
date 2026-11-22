-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_rename_id
-- name    : MatchingLogic.Pattern.rename_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:19.582058+00:00
-- url     : https://prove2.me/theorems/90cd7e6d-cfc0-444b-9729-89bffb28d504
-- title:
--   Pattern: rename id
-- statement:
--   The Pattern construction uses the rename id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L41-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L41-L51

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.rename_id (p : Pattern S Var) : p.rename id = p := by sorry
