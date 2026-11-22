-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_bernWeight_nonnegative
-- name    : HighDimSteinerSpanners.Proofs.CSP.bernWeight_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:00.823008+00:00
-- url     : https://prove2.me/theorems/da2932dd-5410-4dbb-8cc3-7fa8c8ece3fc
-- title:
--   CSP: bern Weight nonnegative
-- statement:
--   The CSP construction uses the bern Weight nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L27-L34
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean#L27-L34

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

theorem HighDimSteinerSpanners.Proofs.CSP.bernWeight_nonnegative {ι : Type} [Fintype ι] (p : ι → ℝ)
  (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : ∀ ω : ι → Bool, 0 ≤ bernWeight p ω := by sorry
