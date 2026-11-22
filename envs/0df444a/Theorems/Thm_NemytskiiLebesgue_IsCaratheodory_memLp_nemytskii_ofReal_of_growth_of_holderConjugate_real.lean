-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_ofReal_of_growth_of_holderConjugate_real
-- name    : NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_ofReal_of_growth_of_holderConjugate_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:23.216503+00:00
-- url     : https://prove2.me/theorems/5632352c-3e68-4c3a-a51e-3c5b512d760f
-- title:
--   Is Caratheodory: mem Lp nemytskii of Real of growth of holder Conjugate real
-- statement:
--   The Is Caratheodory construction uses the mem Lp nemytskii of Real of growth of holder Conjugate real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L209-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L209-L219

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

theorem NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_ofReal_of_growth_of_holderConjugate_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ := by sorry
