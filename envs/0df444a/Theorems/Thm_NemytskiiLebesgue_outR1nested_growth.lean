-- Prove2me | Theorems.Thm_NemytskiiLebesgue_outR1nested_growth
-- name    : NemytskiiLebesgue.outR1nested_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:33.569006+00:00
-- url     : https://prove2.me/theorems/e41a389e-d145-432c-b699-36188ef96ac6
-- title:
--   Nemytskii Lebesgue: out R1nested growth
-- statement:
--   The Nemytskii Lebesgue construction uses the out R1nested growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L113-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L113-L120

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

theorem NemytskiiLebesgue.outR1nested_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ))
    {b : Ω → ℝ} {C α : ℝ}
    (hf'bCα : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖NemytskiiLebesgue.outR1nested f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α := by sorry
