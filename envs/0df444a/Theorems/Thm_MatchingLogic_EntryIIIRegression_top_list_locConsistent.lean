-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_top_list_locConsistent
-- name    : MatchingLogic.EntryIIIRegression.top_list_locConsistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:46.547849+00:00
-- url     : https://prove2.me/theorems/e3d153ed-d241-4f65-ae65-7e89a0f3d1ef
-- title:
--   Entry IIIRegression: top list loc Consistent
-- statement:
--   The Entry IIIRegression construction uses the top list loc Consistent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L238-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L238-L255

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Regression
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set

theorem MatchingLogic.EntryIIIRegression.top_list_locConsistent :
    LocConsistent
      {delta : Pattern AuditSig Nat |
        delta ∈ [(Pattern.tp : Pattern AuditSig Nat)]} := by sorry
