-- Prove2me | Theorems.Thm_NemytskiiLebesgue_norm_realLIE
-- name    : NemytskiiLebesgue.norm_realLIE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:39.099345+00:00
-- url     : https://prove2.me/theorems/c68d1c05-060c-46ba-8bb3-0bcc37a8df9e
-- title:
--   Nemytskii Lebesgue: norm real LIE
-- statement:
--   The Nemytskii Lebesgue construction uses the norm real LIE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L35-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L35-L35

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal

theorem NemytskiiLebesgue.norm_realLIE (r : ℝ) : ‖realLIE r‖ = |r| := by sorry
