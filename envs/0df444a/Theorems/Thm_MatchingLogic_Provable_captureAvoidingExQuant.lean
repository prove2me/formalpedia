-- Prove2me | Theorems.Thm_MatchingLogic_Provable_captureAvoidingExQuant
-- name    : MatchingLogic.Provable.captureAvoidingExQuant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:46.055016+00:00
-- url     : https://prove2.me/theorems/c7c2181d-cda0-4700-8e16-72023f74954e
-- title:
--   Provable: capture Avoiding Ex Quant
-- statement:
--   The Provable construction uses the capture Avoiding Ex Quant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L411-L419
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L411-L419

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

theorem MatchingLogic.Provable.captureAvoidingExQuant {Gamma : Set (Pattern S Nat)}
    (x y : Nat) (p : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.captureAvoidingSubst x y p) (.ex x p)) := by sorry
