-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_of_holderConjugate
-- name    : NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth_of_holderConjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:56.783583+00:00
-- url     : https://prove2.me/theorems/b49f752d-964f-42d0-acf8-ad7f9e534591
-- title:
--   Is Caratheodory: mem Lp nemytskii of growth of holder Conjugate
-- statement:
--   The Is Caratheodory construction uses the mem Lp nemytskii of growth of holder Conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L126-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L126-L147

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology

theorem NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth_of_holderConjugate
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {f : Ω → D → D} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q))
    {u : Ω → D} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ := by sorry
