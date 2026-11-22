-- Prove2me | Theorems.Thm_NemytskiiLebesgue_convergesTo_of_tendsTo_of_growth_of_aestronglyMeas
-- name    : NemytskiiLebesgue.convergesTo_of_tendsTo_of_growth_of_aestronglyMeas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:05.522669+00:00
-- url     : https://prove2.me/theorems/ebbce10f-1537-4a6d-9422-5912a95ec660
-- title:
--   Nemytskii Lebesgue: converges To of tends To of growth of aestrongly Meas
-- statement:
--   The Nemytskii Lebesgue construction uses the converges To of tends To of growth of aestrongly Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L149-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L149-L181

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

theorem NemytskiiLebesgue.convergesTo_of_tendsTo_of_growth_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {f : ℕ → Ω → F} (f_meas : ∀ n : ℕ, AEStronglyMeasurable (f n) μ)
    {g : Ω → F} (hgp : MemLp g p μ)
    {l : Ω → ℝ} (hlp : MemLp l p μ)
    (hfl : ∀ n : ℕ, ∀ᵐ ω : Ω ∂μ, ‖f n ω‖ ≤ l ω)
    (hfg : ∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    f.NemytskiiConvergesTo g p μ := by sorry
