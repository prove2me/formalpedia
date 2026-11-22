-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integral_nemytskii_inner_ge_of_ae_all_inner_ge_of_growth
-- name    : NemytskiiLebesgue.IsCaratheodory.integral_nemytskii_inner_ge_of_ae_all_inner_ge_of_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:29.23598+00:00
-- url     : https://prove2.me/theorems/522fb2ec-95e7-41aa-8abf-4dd65eb0d945
-- title:
--   Is Caratheodory: integral nemytskii inner ge of ae all inner ge of growth
-- statement:
--   The Is Caratheodory construction uses the integral nemytskii inner ge of ae all inner ge of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L182-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L182-L207

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

theorem NemytskiiLebesgue.IsCaratheodory.integral_nemytskii_inner_ge_of_ae_all_inner_ge_of_growth
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {b : Ω → ℝ} (hb1 : Integrable b μ)
    {C₂ : ℝ} (hfCpb : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ⟪f ω ξ, ξ⟫ ≥ C₂ * ‖ξ‖ ^ p - b ω)
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ ∧
    Integrable (fun ω : Ω => ⟪f ω (u ω), u ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω), u ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω‖ ^ p ∂μ - ∫ ω : Ω, |b ω| ∂μ := by sorry
