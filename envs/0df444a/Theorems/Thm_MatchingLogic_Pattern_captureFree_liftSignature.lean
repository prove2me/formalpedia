-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureFree_liftSignature
-- name    : MatchingLogic.Pattern.captureFree_liftSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:38.981917+00:00
-- url     : https://prove2.me/theorems/e467c333-3601-4173-ba00-4b7605609dbd
-- title:
--   Pattern: capture Free lift Signature
-- statement:
--   Capture-freedom is preserved when a pattern is lifted to a larger signature.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L127-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L127-L142

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

theorem MatchingLogic.Pattern.captureFree_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    {x y : Var} {p : Pattern (S.restrict F) Var} :
    CaptureFree x y p → CaptureFree x y (p.liftSignature F) := by sorry
