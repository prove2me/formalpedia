-- Prove2me | Theorems.Thm_NemytskiiLebesgue_Filter_Tendsto_extract_fast_subseq_eLpNorm
-- name    : NemytskiiLebesgue.Filter.Tendsto.extract_fast_subseq_eLpNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:41.504074+00:00
-- url     : https://prove2.me/theorems/93247b37-2311-4701-bdd0-bdfce8883c57
-- title:
--   Tendsto: extract fast subseq e Lp Norm
-- statement:
--   The Tendsto construction uses the extract fast subseq e Lp Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L267-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L267-L274

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

theorem NemytskiiLebesgue.Filter.Tendsto.extract_fast_subseq_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {l : ℕ → Ω → E} (hlp : Tendsto (fun n : ℕ => eLpNorm (l n) p μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k : ℕ, eLpNorm (l (s k)) p μ ≤ ↱(1 / 2 ^ k) := by sorry
