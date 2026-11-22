-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_raw_degree_and_edge_second_moment_sums
-- name    : HighDimSteinerSpanners.Proofs.CSP.raw_degree_and_edge_second_moment_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:07.213347+00:00
-- url     : https://prove2.me/theorems/2ab94288-b9e8-4082-a9e9-e7650cc35fd7
-- title:
--   CSP: raw degree and edge second moment sums
-- statement:
--   The CSP construction uses the raw degree and edge second moment sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/EdgeMoments.lean#L1620-L1703
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/EdgeMoments.lean#L1620-L1703

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_EdgeMoments
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.raw_degree_and_edge_second_moment_sums (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 *
    C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hp_edge_lt1 : cspPEdge C₁ r_star < 1)
    (h_cal : (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (-(cspGamma0 C₁ : ℝ)))
    (hσ_low : (cspBeta0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2)
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (h_union_card : ∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2)
    (h_M0 : ∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          dHam xy.1 xy.2 = r_star),
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card =
      cspN0 C₁ r_star * cspDStar C₁ r_star) :
    (∑ xyz ∈ Finset.univ.filter
        (fun xyz : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                   (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                   (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          dHam xyz.1 xyz.2.1 = r_star ∧ dHam xyz.1 xyz.2.2 = r_star ∧ xyz.2.1 ≠ xyz.2.2),
      (cspPKeep C₁ r_star) ^ 3 *
        (cspPEdge C₁ r_star) ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
        (3 / 2 : ℝ) * cspGamma r_star *
          cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2) ∧
    (∑ e₁₂ ∈ Finset.univ.filter
        (fun e₁₂ : ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                    (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) ×
                   ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                    (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) =>
          dHam e₁₂.1.1 e₁₂.1.2 = r_star ∧ dHam e₁₂.2.1 e₁₂.2.2 = r_star ∧
          e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
          e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2),
      (cspPKeep C₁ r_star) ^ 4 *
        (cspPEdge C₁ r_star) ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                                homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card ≤
        2 * cspGamma r_star *
          (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2) := by sorry
