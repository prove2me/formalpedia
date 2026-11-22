-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_difference_le_of_lipschitz
-- name    : NemytskiiLebesgue.integralLpNorm_difference_le_of_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:53.01503+00:00
-- url     : https://prove2.me/theorems/f58caaa0-bafd-45c8-9fd6-4cfd939d26d0
-- title:
--   Nemytskii Lebesgue: integral Lp Norm difference le of lipschitz
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm difference le of lipschitz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L68-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L68-L89

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal

theorem NemytskiiLebesgue.integralLpNorm_difference_le_of_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {L : Ω → ℝ} (hL : AEStronglyMeasurable L μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖)
    {u v : Ω → D} (huv : AEStronglyMeasurable (u - v) μ)
    (p : ℝ≥0∞) :
    integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ ≤ eLpNorm L ⊤ μ * eLpNorm (u - v) p μ
      := by sorry
