-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_dyadic_linear_growth
-- name    : HighDimSteinerSpanners.Proofs.CSP.dyadic_linear_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:18.6942+00:00
-- url     : https://prove2.me/theorems/4b637d19-d17e-4d2a-a89d-a0897a419056
-- title:
--   CSP: dyadic linear growth
-- statement:
--   The CSP construction uses the dyadic linear growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L33-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L33-L42

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.dyadic_linear_growth : ∀ m : ℕ, 20 ≤ m → 20000 * (m + 2) ≤ 2 ^ m := by sorry
