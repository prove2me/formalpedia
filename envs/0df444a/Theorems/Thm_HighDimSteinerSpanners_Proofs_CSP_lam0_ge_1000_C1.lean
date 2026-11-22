-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_lam0_ge_1000_C1
-- name    : HighDimSteinerSpanners.Proofs.CSP.lam0_ge_1000_C1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:47:03.691865+00:00
-- url     : https://prove2.me/theorems/49882744-bfce-4da3-af45-b964637f8863
-- title:
--   CSP: lam0 ge 1000 C1
-- statement:
--   The CSP construction uses the lam0 ge 1000 C1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CalibrationBounds.lean#L33-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CalibrationBounds.lean#L33-L98

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

theorem HighDimSteinerSpanners.Proofs.CSP.lam0_ge_1000_C1 (C₁ : ℕ) (hC₁ : 3 ≤ C₁) :
    2 ≤ Nat.clog 2 C₁ ∧ 1000 * C₁ ≤ cspLam0 C₁ ∧
    (cspL C₁ : ℝ) ≤ (2000000 : ℝ) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by sorry
