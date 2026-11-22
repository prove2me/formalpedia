-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_globally_lipschitz
-- name    : NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_globally_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:32.472202+00:00
-- url     : https://prove2.me/theorems/dd1d5744-111b-42f3-bd8f-0722e025bd23
-- title:
--   Is Caratheodory: mem Lp nemytskii of globally lipschitz
-- statement:
--   The Is Caratheodory construction uses the mem Lp nemytskii of globally lipschitz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L52-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L52-L66

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

theorem NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_globally_lipschitz
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (hf0p : MemLp (f · 0) p μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    {L : Ω → ℝ} (hL : MemLp L ⊤ μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖) :
    MemLp (fun ω : Ω => f ω (u ω)) p μ := by sorry
