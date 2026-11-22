-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_monotone_integral_real
-- name    : NemytskiiLebesgue.IsCaratheodory.monotone_integral_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:19.345596+00:00
-- url     : https://prove2.me/theorems/2c49736a-2d0c-458f-a4df-f10d34297389
-- title:
--   Is Caratheodory: monotone integral real
-- statement:
--   The Is Caratheodory construction uses the monotone integral real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Nemytskii.lean#L48-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Nemytskii.lean#L48-L62

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

theorem NemytskiiLebesgue.IsCaratheodory.monotone_integral_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ → ℝ} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q))
    (hf0 : ∀ᵐ ω ∂μ, ∀ s t : ℝ, (f ω s - f ω t) * (s - t) ≥ 0)
    {u : Ω → ℝ} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f ω (u ω) - f ω (v ω)) * (u ω - v ω)) μ ∧
    0 ≤ ∫ ω : Ω, (f ω (u ω) - f ω (v ω)) * (u ω - v ω) ∂μ := by sorry
