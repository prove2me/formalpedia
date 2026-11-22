-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_extendSignature_liftSignature
-- name    : MatchingLogic.Model.denote_extendSignature_liftSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:58.704+00:00
-- url     : https://prove2.me/theorems/92336d92-e2f7-4592-8093-a9718357e938
-- title:
--   Model: denote extend Signature lift Signature
-- statement:
--   Denotation is preserved when a restricted pattern is lifted and its model
--   is extended by empty interpretations outside the restricted signature.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L111-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L111-L137

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Theorems.Thm_MatchingLogic_Provable_liftSignature

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Model

theorem MatchingLogic.Model.denote_extendSignature_liftSignature [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (p : Pattern (S.restrict F) Var) :
    (M.extendSignature F).denote rho (p.liftSignature F) = M.denote rho p := by sorry
