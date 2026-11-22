-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integral_inner_ge_of_ae_inner_ge_of_integrable
-- name    : NemytskiiLebesgue.integral_inner_ge_of_ae_inner_ge_of_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:57.587291+00:00
-- url     : https://prove2.me/theorems/29f410b1-df20-4d45-a1e8-fa8ab6fc28fc
-- title:
--   Nemytskii Lebesgue: integral inner ge of ae inner ge of integrable
-- statement:
--   The Nemytskii Lebesgue construction uses the integral inner ge of ae inner ge of integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L168-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L168-L180

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology

theorem NemytskiiLebesgue.integral_inner_ge_of_ae_inner_ge_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {g u : Ω → ℝ^k} (hgu : Integrable (fun ω : Ω => ⟪g ω, u ω⟫) μ)
    {b : Ω → ℝ} (hb : Integrable b μ)
    {p : ℝ} (hup : Integrable (‖u ·‖ ^ p) μ)
    {C : ℝ} (hguCupb : ∀ᵐ ω ∂μ, ⟪g ω, u ω⟫ ≥ C * ‖u ω‖ ^ p - b ω) :
    ∫ ω : Ω, ⟪g ω, u ω⟫ ∂μ ≥ C * ∫ ω : Ω, ‖u ω‖ ^ p ∂μ - ∫ ω : Ω, |b ω| ∂μ := by sorry
