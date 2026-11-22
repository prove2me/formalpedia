-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_finite_model_existence_returns_actual_point
-- name    : MatchingLogic.EntryIIIRegression.finite_model_existence_returns_actual_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:04.005898+00:00
-- url     : https://prove2.me/theorems/8704c644-18b5-487e-999f-095194e27a91
-- title:
--   Entry IIIRegression: finite model existence returns actual point
-- statement:
--   Finite model existence returns a concrete model, valuation, and carrier point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L258-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L258-L264

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

theorem MatchingLogic.EntryIIIRegression.finite_model_existence_returns_actual_point :
    ∃ (M : Model AuditSig) (rho : Nat → M.carrier) (u : M.carrier),
      u ∈ M.denoteSet rho
        {delta : Pattern AuditSig Nat |
          delta ∈ [(Pattern.tp : Pattern AuditSig Nat)]} := by sorry
