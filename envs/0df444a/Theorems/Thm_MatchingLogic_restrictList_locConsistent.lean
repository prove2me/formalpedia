-- Prove2me | Theorems.Thm_MatchingLogic_restrictList_locConsistent
-- name    : MatchingLogic.restrictList_locConsistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:50.12381+00:00
-- url     : https://prove2.me/theorems/7cd729fa-39de-4b68-8039-1968700db2cd
-- title:
--   Matching Logic: restrict List loc Consistent
-- statement:
--   Restricting a locally consistent supported finite list preserves local
--   consistency: a contradiction over the restricted signature would lift to one
--   over the original list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L184-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L184-L203

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

theorem MatchingLogic.restrictList_locConsistent [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern S Var)) (hsupport : ∀ p ∈ l, p.symbolSupport ⊆ F)
    (hconsistent : LocConsistent {delta | delta ∈ l}) :
    LocConsistent {delta | delta ∈ Pattern.restrictList F l hsupport} := by sorry
