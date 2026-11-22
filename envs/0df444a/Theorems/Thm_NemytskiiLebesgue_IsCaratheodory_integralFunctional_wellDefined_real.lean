-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integralFunctional_wellDefined_real
-- name    : NemytskiiLebesgue.IsCaratheodory.integralFunctional_wellDefined_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:54.843045+00:00
-- url     : https://prove2.me/theorems/ca8d0a70-38bc-4fb7-a1be-4ed66c77a541
-- title:
--   Is Caratheodory: integral Functional well Defined real
-- statement:
--   The Is Caratheodory construction uses the integral Functional well Defined real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L52-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L52-L62

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

theorem NemytskiiLebesgue.IsCaratheodory.integralFunctional_wellDefined_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ := by sorry
