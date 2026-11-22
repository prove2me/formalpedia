-- Prove2me | Theorems.Thm_MatchingLogic_locConsistent_extend_isMCS
-- name    : MatchingLogic.locConsistent_extend_isMCS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:00.797791+00:00
-- url     : https://prove2.me/theorems/c2566caf-2b19-4252-9447-0d1844993c1e
-- title:
--   Matching Logic: loc Consistent extend is MCS
-- statement:
--   Every locally consistent pattern set is included in a maximal locally
--   consistent set.  This is the non-witnessed Zorn part of the source's
--   Lindenbaum construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Lindenbaum.lean#L72-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Lindenbaum.lean#L72-L87

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Mathlib.Order.Zorn
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.locConsistent_extend_isMCS {Gamma : Set (Pattern S Var)}
    (hGamma : LocConsistent Gamma) :
    ∃ Delta : Set (Pattern S Var), Gamma ⊆ Delta ∧ IsMCS Delta := by sorry
