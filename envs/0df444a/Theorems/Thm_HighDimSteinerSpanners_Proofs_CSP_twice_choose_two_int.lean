-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two_int
-- name    : HighDimSteinerSpanners.Proofs.CSP.twice_choose_two_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:06.086518+00:00
-- url     : https://prove2.me/theorems/1a774c05-c7df-40ac-bb7f-44c035dfa332
-- title:
--   CSP: twice choose two int
-- statement:
--   The CSP construction uses the twice choose two int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L60-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L60-L70

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

theorem HighDimSteinerSpanners.Proofs.CSP.twice_choose_two_int : ∀ m : ℕ, 2 * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by sorry
