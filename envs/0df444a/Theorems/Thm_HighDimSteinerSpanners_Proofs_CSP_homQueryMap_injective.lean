-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_homQueryMap_injective
-- name    : HighDimSteinerSpanners.Proofs.CSP.homQueryMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:21.191505+00:00
-- url     : https://prove2.me/theorems/5daec979-eaa6-4c70-9108-08b435d0268f
-- title:
--   CSP: hom Query Map injective
-- statement:
--   The CSP construction uses the hom Query Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L134-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L134-L139

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

theorem HighDimSteinerSpanners.Proofs.CSP.homQueryMap_injective {N q : ℕ} : ∀ z : Fin N → Fin q,
    Function.Injective (fun uv : Fin N × Fin N => (uv.1, uv.2, z uv.1, z uv.2)) := by sorry
