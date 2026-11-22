-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_choose_two_le_product
-- name    : HighDimSteinerSpanners.Proofs.CSP.choose_two_le_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:09.00501+00:00
-- url     : https://prove2.me/theorems/bff00617-c2b0-4491-87da-39cc0631ca91
-- title:
--   CSP: choose two le product
-- statement:
--   The CSP construction uses the choose two le product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L77-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L77-L85

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

theorem HighDimSteinerSpanners.Proofs.CSP.choose_two_le_product {N : ℕ} : ∀ s : ℕ, s ≤ N → s.choose 2 ≤ s * (N - 1) := by sorry
