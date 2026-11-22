-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_d3_and_cherry_query_sum_bounds
-- name    : HighDimSteinerSpanners.Proofs.CSP.d3_and_cherry_query_sum_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:54.182269+00:00
-- url     : https://prove2.me/theorems/039bc34a-e1a7-4404-a0db-95337e051154
-- title:
--   CSP: d3 and cherry query sum bounds
-- statement:
--   The CSP construction uses the d3 and cherry query sum bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L1165-L1351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean#L1165-L1351

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.d3_and_cherry_query_sum_bounds (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ <
    r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hp_edge_lt1 : cspPEdge C₁ r_star < 1)
    (h_cal : (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (-(cspGamma0 C₁ : ℝ)))
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :
    (∀ x u : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁), dHam x u ≤ C₁ * r_star →
      ∑ z ∈ Finset.univ.filter (fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
          dHam x z ≤ C₁ * r_star ∧
          r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card),
        (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries x ∪ homQueries u)).card) ≤
        (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ∧
    (∀ x w₀ : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁), dHam x w₀ ≤ C₁ * r_star →
      ∀ m < cspKCh C₁, ∀ y_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, y_prev t ∈ cspPoolCh C₁ r_star x w₀) →
        ∑ y ∈ cspPoolCh C₁ r_star x w₀ \ Finset.univ.image y_prev,
          (∏ i ∈ (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
              (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev,
            cspPIota C₁ r_star i) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by sorry
