-- Prove2me | Theorems.Thm_MatchingLogic_Model_app_extendSignature
-- name    : MatchingLogic.Model.app_extendSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:52.056009+00:00
-- url     : https://prove2.me/theorems/5ffe4ae2-a7e8-47cb-a121-b66d352ab57a
-- title:
--   Model: app extend Signature
-- statement:
--   On a retained symbol, pointwise application is unchanged by extension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L94-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L94-L107

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Model

theorem MatchingLogic.Model.app_extendSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (M : Model (S.restrict F)) (sigma : (S.restrict F).Sym)
    (A : Fin (S.arity sigma.1) → Set M.carrier) :
    (M.extendSignature F).app sigma.1 A = M.app sigma A := by sorry
