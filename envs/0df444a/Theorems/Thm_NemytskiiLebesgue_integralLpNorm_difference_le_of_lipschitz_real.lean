-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_difference_le_of_lipschitz_real
-- name    : NemytskiiLebesgue.integralLpNorm_difference_le_of_lipschitz_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:37.258603+00:00
-- url     : https://prove2.me/theorems/a510f565-ec5b-4956-b692-7f9837734a95
-- title:
--   Nemytskii Lebesgue: integral Lp Norm difference le of lipschitz real
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm difference le of lipschitz real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L91-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L91-L102

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

theorem NemytskiiLebesgue.integralLpNorm_difference_le_of_lipschitz_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {L : Ω → ℝ} (hL : AEMeasurable L μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖)
    {p : ℝ≥0∞}
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v p μ) :
    integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ ≤ eLpNorm L ⊤ μ * eLpNorm (u - v) p μ := by sorry
