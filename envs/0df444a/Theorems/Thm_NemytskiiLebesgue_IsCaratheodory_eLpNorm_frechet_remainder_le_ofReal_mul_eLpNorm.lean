-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
-- name    : NemytskiiLebesgue.IsCaratheodory.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:42.241517+00:00
-- url     : https://prove2.me/theorems/79b093d8-6918-4ac7-be71-a84b61cd6b52
-- title:
--   Is Caratheodory: e Lp Norm frechet remainder le of Real mul e Lp Norm
-- statement:
--   The Is Caratheodory construction uses the e Lp Norm frechet remainder le of Real mul e Lp Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L429-L501
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L429-L501

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

theorem NemytskiiLebesgue.IsCaratheodory.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q r : ℝ} (h1p : 1 ≤ p) (h1r : 1 ≤ r) (hrpq : Real.HolderTriple r p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbr : MemLp b ↱r μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          eLpNorm (fun ω : Ω => f ω (u ω + l ω) - f ω (u ω) - f' ω (u ω) (l ω)) ↱q μ ≤
          ↱ε * eLpNorm l ↱p μ := by sorry
