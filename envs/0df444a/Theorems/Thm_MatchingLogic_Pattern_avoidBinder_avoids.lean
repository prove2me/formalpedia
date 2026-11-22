-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_avoidBinder_avoids
-- name    : MatchingLogic.Pattern.avoidBinder_avoids
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:08.63845+00:00
-- url     : https://prove2.me/theorems/6b3f4bd5-f52c-47ed-8c49-4e1bc2f2094e
-- title:
--   Pattern: avoid Binder avoids
-- statement:
--   The Pattern construction uses the avoid Binder avoids property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L280-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L280-L300

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

theorem MatchingLogic.Pattern.avoidBinder_avoids (y : Nat) (p : Pattern S Nat) :
    AvoidsBinder y (avoidBinder y p) := by sorry
