-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_nemytskii_rpow_le_of_growth_real
-- name    : NemytskiiLebesgue.integralLpNorm_nemytskii_rpow_le_of_growth_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:19.878584+00:00
-- url     : https://prove2.me/theorems/2c646c5e-bc08-4db9-9e77-1b7dcb3289fb
-- title:
--   Nemytskii Lebesgue: integral Lp Norm nemytskii rpow le of growth real
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm nemytskii rpow le of growth real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L118-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L118-L132

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

theorem NemytskiiLebesgue.integralLpNorm_nemytskii_rpow_le_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    (u : Ω → ℝ^m) :
    integralLpNorm (fun ω : Ω => f ω (u ω)) q μ ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * integralLpNorm a q μ ^ q.toReal +
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * ↱C ^ q.toReal * integralLpNorm u p μ ^ p.toReal := by sorry
