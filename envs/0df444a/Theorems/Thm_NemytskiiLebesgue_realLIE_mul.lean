-- Prove2me | Theorems.Thm_NemytskiiLebesgue_realLIE_mul
-- name    : NemytskiiLebesgue.realLIE_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:13.296246+00:00
-- url     : https://prove2.me/theorems/9131b1e2-b26f-4dc8-afc1-dae80a86d6bc
-- title:
--   Nemytskii Lebesgue: real LIE mul
-- statement:
--   The Nemytskii Lebesgue construction uses the real LIE mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L37-L38
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L37-L38

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

theorem NemytskiiLebesgue.realLIE_mul (c s : ℝ) : realLIE (c * s) = c • realLIE s := by sorry
