-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_nemytskii_rpow_le_of_growth
-- name    : NemytskiiLebesgue.integralLpNorm_nemytskii_rpow_le_of_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:51.957323+00:00
-- url     : https://prove2.me/theorems/e4473617-c792-44d7-9998-e69f5effb5be
-- title:
--   Nemytskii Lebesgue: integral Lp Norm nemytskii rpow le of growth
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm nemytskii rpow le of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L26-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L26-L116

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

theorem NemytskiiLebesgue.integralLpNorm_nemytskii_rpow_le_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : AEMeasurable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    (u : Ω → D) :
    integralLpNorm (fun ω : Ω => f ω (u ω)) q μ ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * integralLpNorm a q μ ^ q.toReal +
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * ↱C ^ q.toReal * integralLpNorm u p μ ^ p.toReal := by sorry
