-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_deriv
-- name    : NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:40.40662+00:00
-- url     : https://prove2.me/theorems/4beb48cc-2026-409d-bbc1-4b5b72d5fdbb
-- title:
--   Is Caratheodory: mem Lp nemytskii deriv
-- statement:
--   The Is Caratheodory construction uses the mem Lp nemytskii deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L124-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L124-L158

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

theorem NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfbCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ := by sorry
