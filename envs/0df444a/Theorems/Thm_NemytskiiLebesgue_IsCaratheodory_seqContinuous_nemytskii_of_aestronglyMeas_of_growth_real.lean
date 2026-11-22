-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_seqContinuous_nemytskii_of_aestronglyMeas_of_growth_real
-- name    : NemytskiiLebesgue.IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:15.915506+00:00
-- url     : https://prove2.me/theorems/723f8cef-c149-4931-963c-ebcd4193bcae
-- title:
--   Is Caratheodory: seq Continuous nemytskii of aestrongly Meas of growth real
-- statement:
--   The Is Caratheodory construction uses the seq Continuous nemytskii of aestrongly Meas of growth real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L151-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L151-L166

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

theorem NemytskiiLebesgue.IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → ℝ^m} (huₙ : ∀ n : ℕ, AEMeasurable (uₙ n) μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    (huuₙ : TendstoInMeasure μ uₙ atTop u)
    (hpuₙ : UnifIntegrable uₙ p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by sorry
