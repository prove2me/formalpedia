-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_choose_bound_exp4
-- name    : HighDimSteinerSpanners.Proofs.CSP.choose_bound_exp4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:02.834927+00:00
-- url     : https://prove2.me/theorems/c1c82439-d9d9-4511-a808-55b271eff606
-- title:
--   CSP: choose bound exp4
-- statement:
--   The CSP construction uses the choose bound exp4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CalibrationBounds.lean#L100-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CalibrationBounds.lean#L100-L121

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

theorem HighDimSteinerSpanners.Proofs.CSP.choose_bound_exp4 (U S m_sz r B : ℕ) (hB : 1 ≤ B) (hU : U ≤ B * r) (hS : S ≤ m_sz) :
    (U.choose S : ℝ) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r := by sorry
