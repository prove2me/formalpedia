-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_frechet_remainder
-- name    : NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_frechet_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:20.088462+00:00
-- url     : https://prove2.me/theorems/f941ce5e-4536-4784-b33e-efa5dda668be
-- title:
--   Is Caratheodory: aestrongly Meas frechet remainder
-- statement:
--   The Is Caratheodory construction uses the aestrongly Meas frechet remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L150-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L150-L167

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology

theorem NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_frechet_remainder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    {p : ℝ} {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {u' : Ω → ℝ^m} (hu' : AEStronglyMeasurable u' μ) :
    AEStronglyMeasurable
      (fun ω : Ω => f ω (u ω + u' ω) - f ω (u ω) - f' ω (u ω) (u' ω))
      μ := by sorry
