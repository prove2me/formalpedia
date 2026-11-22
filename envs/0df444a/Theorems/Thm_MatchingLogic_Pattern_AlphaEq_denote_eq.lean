-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_AlphaEq_denote_eq
-- name    : MatchingLogic.Pattern.AlphaEq.denote_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:09.423835+00:00
-- url     : https://prove2.me/theorems/b9960e1f-ff45-4a12-ba36-ffaa79565cf1
-- title:
--   Alpha Eq: denote eq
-- statement:
--   The Alpha Eq construction uses the denote eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L214-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L214-L237

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
open MatchingLogic.Pattern.AlphaEq

theorem MatchingLogic.Pattern.AlphaEq.denote_eq {p q : Pattern S Nat} (h : AlphaEq p q)
    (M : Model S) (rho : Nat → M.carrier) : M.denote rho p = M.denote rho q := by sorry
