-- Prove2me | Theorems.Thm_NemytskiiLebesgue_norm_integral_le_eLpNorm_one_toReal
-- name    : NemytskiiLebesgue.norm_integral_le_eLpNorm_one_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:29.280082+00:00
-- url     : https://prove2.me/theorems/f4b8ef29-cfcb-48c1-9ccf-7b02d0246877
-- title:
--   Nemytskii Lebesgue: norm integral le e Lp Norm one to Real
-- statement:
--   The Nemytskii Lebesgue construction uses the norm integral le e Lp Norm one to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L182-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L182-L191

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal

theorem NemytskiiLebesgue.norm_integral_le_eLpNorm_one_toReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : Ω → ℝ) :
    ‖∫ ω : Ω, g ω ∂μ‖ ≤ (eLpNorm g 1 μ).toReal := by sorry
