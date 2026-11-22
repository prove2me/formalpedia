-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integrable_nemytskii_deriv_apply
-- name    : NemytskiiLebesgue.IsCaratheodory.integrable_nemytskii_deriv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:27.30092+00:00
-- url     : https://prove2.me/theorems/f299562f-3f2e-4a35-a70a-199a5cd1abce
-- title:
--   Is Caratheodory: integrable nemytskii deriv apply
-- statement:
--   The Is Caratheodory construction uses the integrable nemytskii deriv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L160-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L160-L180

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

theorem NemytskiiLebesgue.IsCaratheodory.integrable_nemytskii_deriv_apply
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ := by sorry
