-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_seqContinuous_nemytskii_of_aestronglyMeas_of_growth
-- name    : NemytskiiLebesgue.IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:45.336219+00:00
-- url     : https://prove2.me/theorems/72e7c71d-e01b-4322-a041-107df353890a
-- title:
--   Is Caratheodory: seq Continuous nemytskii of aestrongly Meas of growth
-- statement:
--   The Is Caratheodory construction uses the seq Continuous nemytskii of aestrongly Meas of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L134-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L134-L149

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

theorem NemytskiiLebesgue.IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D F : Type*} [NormedAddCommGroup D] [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → D} (huₙ : ∀ n : ℕ, AEStronglyMeasurable (uₙ n) μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (huuₙ : TendstoInMeasure μ uₙ atTop u)
    (hpuₙ : UnifIntegrable uₙ p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by sorry
