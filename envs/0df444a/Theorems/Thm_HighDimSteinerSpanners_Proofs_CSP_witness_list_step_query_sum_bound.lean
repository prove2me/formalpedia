-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_witness_list_step_query_sum_bound
-- name    : HighDimSteinerSpanners.Proofs.CSP.witness_list_step_query_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:25.626827+00:00
-- url     : https://prove2.me/theorems/536926de-c311-45be-8205-e2ffe3668663
-- title:
--   CSP: witness list step query sum bound
-- statement:
--   The CSP construction uses the witness list step query sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L764-L996
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L764-L996

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

theorem HighDimSteinerSpanners.Proofs.CSP.witness_list_step_query_sum_bound (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ <
    r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (a b : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))
    (hd_ab : dHam a b ≤ C₁ * r_star) :
    ∃ (M_wit : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        Finset (candWitType (2 ^ cspL C₁ * r_star) C₁))
      (Q_cand : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        candWitType (2 ^ cspL C₁ * r_star) C₁ →
        Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))),
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
        ∀ w ∈ M_wit m z_prev x,
          Q_cand m z_prev x w ⊆
            cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
      (∀ (ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool) (m : ℕ), m < cspKMom C₁ →
        ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ω (Sum.inr x) = true →
          x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
          ∃ w ∈ M_wit m z_prev x, ∀ i ∈ Q_cand m z_prev x w, ω i = true) ∧
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∑ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ∑ w ∈ M_wit m z_prev x, (∏ i ∈ Q_cand m z_prev x w, cspPIota C₁ r_star i) ≤
            (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by sorry
