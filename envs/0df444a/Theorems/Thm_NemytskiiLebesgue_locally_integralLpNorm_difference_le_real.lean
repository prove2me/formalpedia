-- Prove2me | Theorems.Thm_NemytskiiLebesgue_locally_integralLpNorm_difference_le_real
-- name    : NemytskiiLebesgue.locally_integralLpNorm_difference_le_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:44.39053+00:00
-- url     : https://prove2.me/theorems/f8e946c4-d76b-4f53-8c4d-e11f839db70c
-- title:
--   Nemytskii Lebesgue: locally integral Lp Norm difference le real
-- statement:
--   The Nemytskii Lebesgue construction uses the locally integral Lp Norm difference le real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L260-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L260-L278

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

theorem NemytskiiLebesgue.locally_integralLpNorm_difference_le_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {p : ℝ} (h1p : 1 ≤ p)
    {q : ℝ} (h1q : 1 ≤ q)
    {α : ℝ} (hα : 0 ≤ α)
    (hqpα : q = p / (α + 1))
    {C : ℝ} (hC : 0 < C)
    (hfC : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ C * (1 + ‖ξ‖ ^ α + ‖η‖ ^ α) * ‖ξ - η‖)
    {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ u v : Ω → ℝ^m,
        MemLp u ↱p μ →
        MemLp v ↱p μ →
        eLpNorm u ↱p μ ≤ ↱R →
        eLpNorm v ↱p μ ≤ ↱R →
        integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) ↱q μ ≤ ↱L * eLpNorm (u - v) ↱p μ := by sorry
