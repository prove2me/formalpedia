-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ae_frechet_ratio_le_of_ae_all_growth_deriv
-- name    : NemytskiiLebesgue.ae_frechet_ratio_le_of_ae_all_growth_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:32.120923+00:00
-- url     : https://prove2.me/theorems/444d8644-5828-44c6-ad53-446b57a19e74
-- title:
--   Nemytskii Lebesgue: ae frechet ratio le of ae all growth deriv
-- statement:
--   The Nemytskii Lebesgue construction uses the ae frechet ratio le of ae all growth deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L169-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L169-L203

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

theorem NemytskiiLebesgue.ae_frechet_ratio_le_of_ae_all_growth_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hf' : ∀ᵐ ω : Ω ∂μ, Continuous (f' ω))
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {C : ℝ} (hC : 0 < C)
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g)
    {v : Ω → ℝ^m} (hvg : ∀ᵐ ω : Ω ∂μ, ‖v ω‖ ≤ g ω)
    (u : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + v ω) - f ω (u ω) - f' ω (u ω) (v ω)‖ / ‖v ω‖ ≤
      2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r) := by sorry
