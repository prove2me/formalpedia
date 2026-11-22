-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integrable_inner_difference_real
-- name    : NemytskiiLebesgue.IsCaratheodory.integrable_inner_difference_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:25.447298+00:00
-- url     : https://prove2.me/theorems/68ff714c-cbf9-4d72-adc0-6cf0dbcfcbcf
-- title:
--   Is Caratheodory: integrable inner difference real
-- statement:
--   The Is Caratheodory construction uses the integrable inner difference real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L238-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L238-L249

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

theorem NemytskiiLebesgue.IsCaratheodory.integrable_inner_difference_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^k} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ := by sorry
