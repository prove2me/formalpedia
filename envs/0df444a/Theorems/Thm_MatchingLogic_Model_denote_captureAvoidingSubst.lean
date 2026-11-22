-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_captureAvoidingSubst
-- name    : MatchingLogic.Model.denote_captureAvoidingSubst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:08.665277+00:00
-- url     : https://prove2.me/theorems/169fbd01-54ce-4448-a820-4e5174a19f5c
-- title:
--   Model: denote capture Avoiding Subst
-- statement:
--   The Model construction uses the denote capture Avoiding Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L390-L397
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L390-L397

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

theorem MatchingLogic.Model.denote_captureAvoidingSubst (M : Model S)
    (rho : Nat → M.carrier) (x y : Nat) (p : Pattern S Nat) :
    M.denote rho (Pattern.captureAvoidingSubst x y p) =
      M.denote (Function.update rho x (rho y)) p := by sorry
