-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_sequentialTailWeight_nonnegative
-- name    : HighDimSteinerSpanners.Proofs.CSP.sequentialTailWeight_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:06.441798+00:00
-- url     : https://prove2.me/theorems/7eae1734-9570-4876-8ecb-da58dcd2efff
-- title:
--   CSP: sequential Tail Weight nonnegative
-- statement:
--   The CSP construction uses the sequential Tail Weight nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L118-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L118-L137

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.sequentialTailWeight_nonnegative {ι β γ : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq β] (p : ι → ℝ) (Pool : Finset β)
  (M_wit : (m : ℕ) → (Fin m → β) → β → Finset γ)
  (Q : (m : ℕ) → (Fin m → β) → β → γ → Finset ι)
  (hW_nn : ∀ ω, 0 ≤ bernWeight p ω) : ∀ (r m : ℕ) (z_prev : Fin m → β) (Acc : Finset ι) (ω : ι →
      Bool),
    0 ≤ sequentialTailWeight p Pool M_wit Q r m z_prev Acc ω := by sorry
