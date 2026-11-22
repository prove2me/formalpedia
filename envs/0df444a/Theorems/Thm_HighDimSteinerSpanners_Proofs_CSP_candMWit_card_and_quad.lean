-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_card_and_quad
-- name    : HighDimSteinerSpanners.Proofs.CSP.candMWit_card_and_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:16.280366+00:00
-- url     : https://prove2.me/theorems/54ba3dc4-6f82-46f4-a47e-8d54711cd3a7
-- title:
--   CSP: cand MWit card and quad
-- statement:
--   The CSP construction uses the cand MWit card and quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L414-L426
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L414-L426

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.candMWit_card_and_quad {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) ∧
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by sorry
