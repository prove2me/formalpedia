-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_hammingSphere_card
-- name    : HighDimSteinerSpanners.Proofs.CSP.hammingSphere_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:19.673638+00:00
-- url     : https://prove2.me/theorems/17881686-bf40-45de-ba99-4757ca2b77be
-- title:
--   CSP: hamming Sphere card
-- statement:
--   The CSP construction uses the hamming Sphere card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L207-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L207-L268

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

theorem HighDimSteinerSpanners.Proofs.CSP.hammingSphere_card {N q : ℕ} : ∀ (x : Fin N → Fin q) (s : ℕ),
    (Finset.univ.filter (fun y => dHam x y = s)).card = N.choose s * (q - 1) ^ s := by sorry
