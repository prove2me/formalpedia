-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas
-- name    : NemytskiiLebesgue.ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:11.94772+00:00
-- url     : https://prove2.me/theorems/f6e5c6fb-a446-4396-9281-a9852af751f4
-- title:
--   Nemytskii Lebesgue: ae summable norm of tsum e Lp Norm ne top of aestrongly Meas
-- statement:
--   The Nemytskii Lebesgue construction uses the ae summable norm of tsum e Lp Norm ne top of aestrongly Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L193-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L193-L271

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

theorem NemytskiiLebesgue.ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {g : ℕ → Ω → D} (hg : ∀ n : ℕ, AEStronglyMeasurable (g n) μ) (hgp : ∑' n : ℕ, eLpNorm (g n) p μ
      ≠ ⊤) :
    ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω‖) := by sorry
