-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_AvoidsBinder_captureFree
-- name    : MatchingLogic.Pattern.AvoidsBinder.captureFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:01.109373+00:00
-- url     : https://prove2.me/theorems/6b7dafd4-627b-458e-a788-bb95a43d2613
-- title:
--   Avoids Binder: capture Free
-- statement:
--   The Avoids Binder construction uses the capture Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L302-L312
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L302-L312

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

theorem MatchingLogic.Pattern.AvoidsBinder.captureFree {y x : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder y p) : CaptureFree x y p := by sorry
