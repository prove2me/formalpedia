-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ae_norm_frechet_ratio_tendsto_zero
-- name    : NemytskiiLebesgue.ae_norm_frechet_ratio_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:28.61993+00:00
-- url     : https://prove2.me/theorems/d1a68111-ef44-4f05-972a-b6c9ed695a37
-- title:
--   Nemytskii Lebesgue: ae norm frechet ratio tendsto zero
-- statement:
--   The Nemytskii Lebesgue construction uses the ae norm frechet ratio tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L51-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L51-L67

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

theorem NemytskiiLebesgue.ae_norm_frechet_ratio_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {l : ℕ → Ω → ℝ^m} (hl : ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0))
    (u : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ, Tendsto
      (fun n : ℕ => ‖f ω (u ω + l n ω) - f ω (u ω) - f' ω (u ω) (l n ω)‖ / ‖l n ω‖)
      atTop
      (𝓝 0) := by sorry
