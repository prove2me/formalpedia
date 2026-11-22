-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_csp_dyadic_calibration_and_first_moments
-- name    : HighDimSteinerSpanners.Proofs.CSP.csp_dyadic_calibration_and_first_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:15.63552+00:00
-- url     : https://prove2.me/theorems/c63600ac-f839-4b84-88cd-a557b1918032
-- title:
--   CSP: csp dyadic calibration and first moments
-- statement:
--   The CSP construction uses the csp dyadic calibration and first moments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L1523-L1587
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Calibration.lean#L1523-L1587

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

theorem HighDimSteinerSpanners.Proofs.CSP.csp_dyadic_calibration_and_first_moments (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000
    * C₁ < r_star) :
    0 < cspSigmaEdge C₁ r_star ∧
    0 < cspPEdge C₁ r_star ∧ cspPEdge C₁ r_star < 1 ∧
    (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)) ∧
    (cspBeta0 C₁ : ℝ) < cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ∧
    cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 < (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) ∧
    (∀ s : ℕ, ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
      (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ))) ∧
    (∀ s : ℕ, s ≤ 2 ^ cspL C₁ * r_star →
      cspDOmega C₁ r_star s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
          cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))) ∧
    (2 : ℝ) ^ ((997 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤ cspDOmega C₁ r_star r_star ∧
    cspDOmega C₁ r_star r_star ≤
      (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ∧
    0 < cspPKeep C₁ r_star ∧ cspPKeep C₁ r_star < 1 ∧
    cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ∧
    (2 : ℝ) ^ ((99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
      cspN0 C₁ r_star ∧
    cspN0 C₁ r_star ≤
      (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ∧
    (∀ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x).card = (2 ^ cspL C₁ * r_star).choose 2) ∧
    (∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2) ∧
    (∀ (x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (s : ℕ),
      (Finset.univ.filter (fun y => dHam x y = s)).card =
        (2 ^ cspL C₁ * r_star).choose s * (cspQ C₁ - 1) ^ s) ∧
    (∑ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      cspPKeep C₁ r_star * (cspPEdge C₁ r_star) ^ (homQueries x).card = cspN0 C₁ r_star) ∧
    (∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) => dHam xy.1 xy.2 = r_star),
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        cspN0 C₁ r_star * cspDStar C₁ r_star) ∧
    (∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star),
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        cspN0 C₁ r_star *
          (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by sorry
