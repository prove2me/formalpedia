-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integralFunctional_wellDefined
-- name    : NemytskiiLebesgue.IsCaratheodory.integralFunctional_wellDefined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:26.159346+00:00
-- url     : https://prove2.me/theorems/11c75e11-c441-4e0d-8c5e-1a9117e7462d
-- title:
--   Is Caratheodory: integral Functional well Defined
-- statement:
--   The Is Caratheodory construction uses the integral Functional well Defined property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L29-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L29-L50

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

theorem NemytskiiLebesgue.IsCaratheodory.integralFunctional_wellDefined
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → D} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ := by sorry
