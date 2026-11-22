-- Prove2me | Theorems.Thm_NemytskiiLebesgue_memLp_nemytskii_of_growth_of_aestronglyMeasurable
-- name    : NemytskiiLebesgue.memLp_nemytskii_of_growth_of_aestronglyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:00.15147+00:00
-- url     : https://prove2.me/theorems/c6430504-04de-4a0a-90d7-56963db9d047
-- title:
--   Nemytskii Lebesgue: mem Lp nemytskii of growth of aestrongly Measurable
-- statement:
--   The Nemytskii Lebesgue construction uses the mem Lp nemytskii of growth of aestrongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L36-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L36-L95

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

theorem NemytskiiLebesgue.memLp_nemytskii_of_growth_of_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ≥0∞} (h0p : 0 < p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → D} (hup : MemLp u p μ)
    (hfu : AEStronglyMeasurable (fun ω : Ω => f ω (u ω)) μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ := by sorry
