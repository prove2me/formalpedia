-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo
-- name    : NemytskiiLebesgue.IsCaratheodory.tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:37.801085+00:00
-- url     : https://prove2.me/theorems/66973c1d-7f30-444c-b2f3-4e52fb89412e
-- title:
--   Is Caratheodory: tends To e Lp Norm frechet ratio of ae tends To
-- statement:
--   The Is Caratheodory construction uses the tends To e Lp Norm frechet ratio of ae tends To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L220-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L220-L265

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

theorem NemytskiiLebesgue.IsCaratheodory.tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {C : ℝ} (hC : 0 < C)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbr : MemLp b ↱r μ)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {l : ℕ → Ω → ℝ^m} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g) (hgp : MemLp g ↱p μ)
    (hlg : ∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l n ω‖ ≤ g ω)
    (hl0 : ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm
        (fun ω : Ω => ‖f ω (u ω + l n ω) - f ω (u ω) - f' ω (u ω) (l n ω)‖ / ‖l n ω‖) ↱r μ)
      atTop
      (𝓝 0) := by sorry
