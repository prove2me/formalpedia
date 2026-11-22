-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integralFunctional_frechet_deriv
-- name    : NemytskiiLebesgue.IsCaratheodory.integralFunctional_frechet_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:56.317603+00:00
-- url     : https://prove2.me/theorems/9bf262af-e4b2-43e3-8bc1-7a966512e5ca
-- title:
--   Is Caratheodory: integral Functional frechet deriv
-- statement:
--   The Is Caratheodory construction uses the integral Functional frechet deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L193-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L193-L233

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

theorem NemytskiiLebesgue.IsCaratheodory.integralFunctional_frechet_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    (∀ v : Ω → ℝ^m, MemLp v ↱p μ →
      Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          ‖∫ ω : Ω, (f ω (u ω + l ω) - f ω (u ω) - (f' ω (u ω)) (l ω)) ∂μ‖ ≤
            ε * (eLpNorm l ↱p μ).toReal) := by sorry
