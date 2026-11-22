-- Prove2me | Theorems.Thm_MatchingLogic_Model_denoteSet_extendSignature_liftSignature_list
-- name    : MatchingLogic.Model.denoteSet_extendSignature_liftSignature_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:11.101427+00:00
-- url     : https://prove2.me/theorems/c8e6d76a-b5bd-4ff3-87da-065f24a993af
-- title:
--   Model: denote Set extend Signature lift Signature list
-- statement:
--   Conjunctive denotation of a finite list is unchanged by lifting and model
--   extension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L156-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L156-L177

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

theorem MatchingLogic.Model.denoteSet_extendSignature_liftSignature_list [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (l : List (Pattern (S.restrict F) Var)) :
    (M.extendSignature F).denoteSet rho
        {delta | delta ∈ l.map (Pattern.liftSignature F)} =
      M.denoteSet rho {delta | delta ∈ l} := by sorry
