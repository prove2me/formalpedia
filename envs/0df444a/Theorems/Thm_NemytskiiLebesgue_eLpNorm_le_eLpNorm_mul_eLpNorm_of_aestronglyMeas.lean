-- Prove2me | Theorems.Thm_NemytskiiLebesgue_eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
-- name    : NemytskiiLebesgue.eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:31.330036+00:00
-- url     : https://prove2.me/theorems/3db50147-0c1d-4429-9ae2-d51dc5c8b5c6
-- title:
--   Nemytskii Lebesgue: e Lp Norm le e Lp Norm mul e Lp Norm of aestrongly Meas
-- statement:
--   The Nemytskii Lebesgue construction uses the e Lp Norm le e Lp Norm mul e Lp Norm of aestrongly Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L109-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L109-L118

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

theorem NemytskiiLebesgue.eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {p q r : ℝ} (hrpq : Real.HolderTriple r p q)
    {l : Ω → ℝ^m} (hl : AEStronglyMeasurable l μ)
    {ψ : Ω → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {R : Ω → ℝ^k} (hR : AEStronglyMeasurable R μ)
    (hRψl : ∀ᵐ ω : Ω ∂μ, ‖R ω‖ ≤ ψ ω * ‖l ω‖) :
    eLpNorm R ↱q μ ≤ eLpNorm ψ ↱r μ * eLpNorm l ↱p μ := by sorry
