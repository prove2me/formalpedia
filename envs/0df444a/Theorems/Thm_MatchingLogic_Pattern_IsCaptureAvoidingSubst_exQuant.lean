-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_exQuant
-- name    : MatchingLogic.Pattern.IsCaptureAvoidingSubst.exQuant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:26.865585+00:00
-- url     : https://prove2.me/theorems/fed72d0d-7b3c-489c-a7d8-01de88a22f63
-- title:
--   Is Capture Avoiding Subst: ex Quant
-- statement:
--   The Is Capture Avoiding Subst construction uses the ex Quant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L421-L425
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L421-L425

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

theorem MatchingLogic.Pattern.IsCaptureAvoidingSubst.exQuant {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p q : Pattern S Nat} (h : IsCaptureAvoidingSubst x y p q) :
    Provable Gamma (.imp q (.ex x p)) := by sorry
