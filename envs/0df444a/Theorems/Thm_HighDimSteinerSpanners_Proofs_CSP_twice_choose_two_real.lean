-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two_real
-- name    : HighDimSteinerSpanners.Proofs.CSP.twice_choose_two_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:15.689604+00:00
-- url     : https://prove2.me/theorems/33c6978a-bd56-4ced-bedc-637743043f78
-- title:
--   CSP: twice choose two real
-- statement:
--   The CSP construction uses the twice choose two real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L72-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L72-L75

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

theorem HighDimSteinerSpanners.Proofs.CSP.twice_choose_two_real : ∀ m : ℕ, 2 * (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by sorry
