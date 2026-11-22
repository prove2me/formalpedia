-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_complexity_substVar
-- name    : MatchingLogic.Pattern.complexity_substVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:06.097379+00:00
-- url     : https://prove2.me/theorems/3d6e63a6-2976-4a5c-901a-8239a879672e
-- title:
--   Pattern: complexity subst Var
-- statement:
--   The Pattern construction uses the complexity subst Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L155-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L155-L164

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators

theorem MatchingLogic.Pattern.complexity_substVar (x y : Nat) (p : Pattern S Nat) :
    (substVar x y p).complexity = p.complexity := by sorry
