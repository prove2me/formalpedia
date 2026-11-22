-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_card_le
-- name    : HighDimSteinerSpanners.Proofs.CSP.candMWit_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:28.660801+00:00
-- url     : https://prove2.me/theorems/ba03b3a3-5571-4653-99c0-8f816d2fb811
-- title:
--   CSP: cand MWit card le
-- statement:
--   The CSP construction uses the cand MWit card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L39-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L39-L206

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

theorem HighDimSteinerSpanners.Proofs.CSP.candMWit_card_le {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) := by sorry
