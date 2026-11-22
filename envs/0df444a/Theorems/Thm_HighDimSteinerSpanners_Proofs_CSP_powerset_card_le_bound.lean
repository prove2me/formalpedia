-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_powerset_card_le_bound
-- name    : HighDimSteinerSpanners.Proofs.CSP.powerset_card_le_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:47:58.765276+00:00
-- url     : https://prove2.me/theorems/324c628b-45fc-44bd-a12e-bb7e5d9a1fb4
-- title:
--   CSP: powerset card le bound
-- statement:
--   The CSP construction uses the powerset card le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CalibrationBounds.lean#L123-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CalibrationBounds.lean#L123-L209

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Definitions
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.powerset_card_le_bound {α : Type*} (R_set : Finset α)
    (C₁ A b : ℕ) (hC₁ : 3 ≤ C₁) (hA : A ≤ 21) (hcard : R_set.card ≤ A * C₁ ^ 2 * b) :
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ) ≤
      ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by sorry
