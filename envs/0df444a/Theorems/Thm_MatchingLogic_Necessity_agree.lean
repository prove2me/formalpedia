-- Prove2me | Theorems.Thm_MatchingLogic_Necessity_agree
-- name    : MatchingLogic.Necessity.agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:58.132867+00:00
-- url     : https://prove2.me/theorems/9e501c18-2fd2-44df-bd9c-e4401e51dca9
-- title:
--   Necessity: agree
-- statement:
--   The Necessity construction uses the agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L72-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L72-L74

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]

theorem MatchingLogic.Necessity.agree : AgreeOn (M := M) C (rho (Var := Var)) rho' := by sorry
