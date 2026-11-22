-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_rename_comp
-- name    : MatchingLogic.Pattern.rename_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:12.876396+00:00
-- url     : https://prove2.me/theorems/aa7b842a-a0a1-4e8e-a28f-c16b1e8e0862
-- title:
--   Pattern: rename comp
-- statement:
--   The Pattern construction uses the rename comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L53-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L53-L65

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

theorem MatchingLogic.Pattern.rename_comp (g : Var' → Var'') (f : Var → Var')
    (p : Pattern S Var) :
    (p.rename f).rename g = p.rename (g ∘ f) := by sorry
