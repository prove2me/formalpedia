-- Prove2me | Theorems.Thm_MatchingLogic_Provable_liftSignature
-- name    : MatchingLogic.Provable.liftSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:20.5078+00:00
-- url     : https://prove2.me/theorems/4fb5e148-b5f2-416e-bc87-fb4ed93ad9f8
-- title:
--   Provable: lift Signature
-- statement:
--   A derivation over a finite sub-signature can be replayed over `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L301-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L301-L373

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Provable.liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    {Gamma : Set (Pattern (S.restrict F) Var)} {phi : Pattern (S.restrict F) Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.liftSignature F '' Gamma) (phi.liftSignature F) := by sorry
