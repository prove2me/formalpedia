-- Prove2me | Theorems.Thm_NemytskiiLebesgue_memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
-- name    : NemytskiiLebesgue.memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:35:05.475878+00:00
-- url     : https://prove2.me/theorems/cbe0256f-b564-466a-8bbc-b8e46a09c110
-- title:
--   Nemytskii Lebesgue: mem Lp nemytskii of globally lipschitz of aestrongly Meas
-- statement:
--   The Nemytskii Lebesgue construction uses the mem Lp nemytskii of globally lipschitz of aestrongly Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L26-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L26-L50

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal

theorem NemytskiiLebesgue.memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞}
    {f : Ω → D → F} (hf0p : MemLp (f · 0) p μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (hfu : AEStronglyMeasurable ((fun ω : Ω => f ω (u ω))) μ)
    {L : Ω → ℝ} (hL' : eLpNorm L ⊤ μ < ⊤)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖) :
    MemLp (fun ω : Ω => f ω (u ω)) p μ := by sorry
