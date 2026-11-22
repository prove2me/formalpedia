-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_homQueries_union_card
-- name    : HighDimSteinerSpanners.Proofs.CSP.homQueries_union_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:19.926008+00:00
-- url     : https://prove2.me/theorems/3b17361f-94d1-45f8-8905-8abc0e212dbd
-- title:
--   CSP: hom Queries union card
-- statement:
--   The CSP construction uses the hom Queries union card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L153-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L153-L205

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

theorem HighDimSteinerSpanners.Proofs.CSP.homQueries_union_card {N q : ℕ} (hN_ge1 : 1 ≤ N) : ∀ x y : Fin N → Fin q,
    (homQueries x ∪ homQueries y).card =
      N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2 := by sorry
