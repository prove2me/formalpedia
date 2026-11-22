-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_liftSignature_update
-- name    : MatchingLogic.Pattern.liftSignature_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:38.232724+00:00
-- url     : https://prove2.me/theorems/edd3dc72-f6b4-4245-92aa-e541a5e563e0
-- title:
--   Pattern: lift Signature update
-- statement:
--   Lifting commutes with replacing an argument of an application.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L146-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L146-L155

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
omit [DecidableEq Var]

theorem MatchingLogic.Pattern.liftSignature_update [DecidableEq S.Sym] (F : Finset S.Sym) {n : Nat}
    (args : Fin n → Pattern (S.restrict F) Var) (i : Fin n)
    (p : Pattern (S.restrict F) Var) :
    (fun j => (Function.update args i p j).liftSignature F) =
      Function.update (fun j => (args j).liftSignature F) i (p.liftSignature F) := by sorry
