-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_extendSignature_restrictSignature
-- name    : MatchingLogic.Model.denote_extendSignature_restrictSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:32.631807+00:00
-- url     : https://prove2.me/theorems/f54d9268-6fac-4560-a2dd-59554286a4a3
-- title:
--   Model: denote extend Signature restrict Signature
-- statement:
--   The ambient denotation of a supported pattern equals the denotation of its
--   restriction in the finite sub-signature.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L141-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L141-L152

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

theorem MatchingLogic.Model.denote_extendSignature_restrictSignature [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (p : Pattern S Var) (h : p.symbolSupport ⊆ F) :
    (M.extendSignature F).denote rho p = M.denote rho (p.restrictSignature F h) := by sorry
