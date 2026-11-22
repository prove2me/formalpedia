-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_ordered_pairs_card
-- name    : HighDimSteinerSpanners.Proofs.CSP.ordered_pairs_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:01.256009+00:00
-- url     : https://prove2.me/theorems/d1f1295e-85a0-46e4-9d41-842fab61bb28
-- title:
--   CSP: ordered pairs card
-- statement:
--   The CSP construction uses the ordered pairs card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L91-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L91-L132

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

theorem HighDimSteinerSpanners.Proofs.CSP.ordered_pairs_card {N : ℕ} : ∀ A : Finset (Fin N),
    ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).card = A.card.choose 2 := by sorry
