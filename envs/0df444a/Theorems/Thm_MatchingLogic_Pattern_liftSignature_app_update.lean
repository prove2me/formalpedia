-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_liftSignature_app_update
-- name    : MatchingLogic.Pattern.liftSignature_app_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:42.069246+00:00
-- url     : https://prove2.me/theorems/8f768802-d5d5-47fc-9943-b4992ef9523e
-- title:
--   Pattern: lift Signature app update
-- statement:
--   The lifted form of an application with one replaced argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L159-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L159-L168

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

theorem MatchingLogic.Pattern.liftSignature_app_update [DecidableEq S.Sym] (F : Finset S.Sym)
    (sigma : (S.restrict F).Sym) (args : Fin ((S.restrict F).arity sigma) →
      Pattern (S.restrict F) Var)
    (i : Fin ((S.restrict F).arity sigma)) (p : Pattern (S.restrict F) Var) :
    (Pattern.app sigma (Function.update args i p)).liftSignature F =
      Pattern.app sigma.1
        (Function.update (fun j => (args j).liftSignature F) i (p.liftSignature F)) := by sorry
