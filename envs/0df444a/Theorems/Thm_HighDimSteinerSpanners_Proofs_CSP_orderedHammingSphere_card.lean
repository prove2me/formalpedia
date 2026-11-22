-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_orderedHammingSphere_card
-- name    : HighDimSteinerSpanners.Proofs.CSP.orderedHammingSphere_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:15.617799+00:00
-- url     : https://prove2.me/theorems/1a1d96e8-935b-4b34-ba48-39bd8a2d8488
-- title:
--   CSP: ordered Hamming Sphere card
-- statement:
--   The CSP construction uses the ordered Hamming Sphere card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L270-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L270-L304

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

theorem HighDimSteinerSpanners.Proofs.CSP.orderedHammingSphere_card {N q : ℕ} : ∀ s : ℕ,
    (Finset.univ.filter
      (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s)).card =
      q ^ N * (N.choose s * (q - 1) ^ s) := by sorry
