-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_close_pair_query_sum_bound
-- name    : HighDimSteinerSpanners.Proofs.CSP.close_pair_query_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:33.703231+00:00
-- url     : https://prove2.me/theorems/7ad196be-988c-4d3c-a659-da3e784020c3
-- title:
--   CSP: close pair query sum bound
-- statement:
--   The CSP construction uses the close pair query sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/ClosePairs.lean#L278-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/ClosePairs.lean#L278-L319

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_EdgeMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_ClosePairs
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.close_pair_query_sum_bound (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (hDOm_s : ∀ s : ℕ, s ≤ 2 ^ cspL C₁ * r_star →
      cspDOmega C₁ r_star s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
          cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (hn0_pos : 0 < cspN0 C₁ r_star)
    (h_union_card : ∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2)
     :
    ∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by sorry
