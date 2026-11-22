-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two
-- name    : HighDimSteinerSpanners.Proofs.CSP.twice_choose_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:21.428482+00:00
-- url     : https://prove2.me/theorems/fbceb4f0-437c-46e2-b0bc-8a0731c92384
-- title:
--   CSP: twice choose two
-- statement:
--   The CSP construction uses the twice choose two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L44-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L44-L58

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

theorem HighDimSteinerSpanners.Proofs.CSP.twice_choose_two : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := by sorry
