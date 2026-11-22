-- Prove2me | Theorems.Thm_NemytskiiLebesgue_memLp_realLIE
-- name    : NemytskiiLebesgue.memLp_realLIE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:16.827477+00:00
-- url     : https://prove2.me/theorems/e5f3cbd3-573e-405f-8371-f94218c5f348
-- title:
--   Nemytskii Lebesgue: mem Lp real LIE
-- statement:
--   The Nemytskii Lebesgue construction uses the mem Lp real LIE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L50-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L50-L53

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

theorem NemytskiiLebesgue.memLp_realLIE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} {u : Ω → ℝ} (hu : MemLp u p μ) :
    MemLp (fun ω : Ω => realLIE (u ω)) p μ := by sorry
