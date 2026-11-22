-- Prove2me | Theorems.Thm_NemytskiiLebesgue_eLpNorm_realLIE
-- name    : NemytskiiLebesgue.eLpNorm_realLIE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:40.966227+00:00
-- url     : https://prove2.me/theorems/89eb5188-2c56-4c76-9a16-b4654e099bb4
-- title:
--   Nemytskii Lebesgue: e Lp Norm real LIE
-- statement:
--   The Nemytskii Lebesgue construction uses the e Lp Norm real LIE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L44-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L44-L48

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

theorem NemytskiiLebesgue.eLpNorm_realLIE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (u : Ω → ℝ) :
    eLpNorm (fun ω : Ω => realLIE (u ω)) p μ = eLpNorm u p μ := by sorry
