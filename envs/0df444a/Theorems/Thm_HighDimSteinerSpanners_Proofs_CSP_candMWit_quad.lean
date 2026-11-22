-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_quad
-- name    : HighDimSteinerSpanners.Proofs.CSP.candMWit_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:20.974388+00:00
-- url     : https://prove2.me/theorems/cfa079cb-1070-4941-87ea-d3698249bd5e
-- title:
--   CSP: cand MWit quad
-- statement:
--   The CSP construction uses the cand MWit quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L208-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean#L208-L412

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.candMWit_quad {N q : ℕ} (C₁ r_star m : ℕ)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    let M := candMFresh a b m z_prev x
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by sorry
