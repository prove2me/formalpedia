-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_freshCoordinateFiberCardinality
-- name    : HighDimSteinerSpanners.Proofs.CSP.freshCoordinateFiberCardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:31.717154+00:00
-- url     : https://prove2.me/theorems/62a4f805-ffbc-4b8e-8b79-6a36c5aca325
-- title:
--   CSP: fresh Coordinate Fiber Cardinality
-- statement:
--   The CSP construction uses the fresh Coordinate Fiber Cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L347-L533
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L347-L533

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.freshCoordinateFiberCardinality : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → m < cspKMom C₁ →
    ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)),
    dHam a b ≤ C₁ * r_star →
    (∀ t : Fin m, dHam (z_prev t) a ≤ C₁ * r_star) →
    ∀ s : ℕ,
    ((Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
      ((C₁ * r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by sorry
