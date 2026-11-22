-- Prove2me | Theorems.Thm_NemytskiiLebesgue_convergesTo_of_ae_tendsTo_of_ae_norm_le
-- name    : NemytskiiLebesgue.convergesTo_of_ae_tendsTo_of_ae_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:40.139867+00:00
-- url     : https://prove2.me/theorems/035554e0-2093-4490-9c28-ed8c93c1166d
-- title:
--   Nemytskii Lebesgue: converges To of ae tends To of ae norm le
-- statement:
--   The Nemytskii Lebesgue construction uses the converges To of ae tends To of ae norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L205-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L205-L218

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology

theorem NemytskiiLebesgue.convergesTo_of_ae_tendsTo_of_ae_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {F : ℕ → Ω → E} (hF : ∀ n : ℕ, AEStronglyMeasurable (F n) μ)
    {g : Ω → E} (hg : AEStronglyMeasurable g μ)
    {b : Ω → ℝ} (hbp : MemLp b p μ)
    (hFb : ∀ n : ℕ, ∀ᵐ ω : Ω ∂μ, ‖F n ω‖ ≤ b ω)
    (hgb : ∀ᵐ ω : Ω ∂μ, ‖g ω‖ ≤ b ω)
    (hFg : ∀ᵐ ω : Ω ∂μ, Tendsto (F · ω) atTop (𝓝 (g ω))) :
    F.NemytskiiConvergesTo g p μ := by sorry
