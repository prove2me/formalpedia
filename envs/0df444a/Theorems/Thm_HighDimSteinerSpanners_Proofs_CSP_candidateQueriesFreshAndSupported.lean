-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candidateQueriesFreshAndSupported
-- name    : HighDimSteinerSpanners.Proofs.CSP.candidateQueriesFreshAndSupported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:31.858807+00:00
-- url     : https://prove2.me/theorems/7824b2a3-f51e-4f68-a638-3a01c7219a4f
-- title:
--   CSP: candidate Queries Fresh And Supported
-- statement:
--   The CSP construction uses the candidate Queries Fresh And Supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L139-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessMoments.lean#L139-L345

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

theorem HighDimSteinerSpanners.Proofs.CSP.candidateQueriesFreshAndSupported : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → 1000 * C₁ <
    r_star →
    ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q),
    x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev →
    candMFresh a b m z_prev x ⊆ disagreeSet x a ∩ disagreeSet x b ∧
    (∀ w ∈ candMWit C₁ r_star a b m z_prev x, candQCand C₁ a b m z_prev x w ⊆
      cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
    (∀ ω : cspIota N q → Bool, ω (Sum.inr x) = true →
      x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
      ∃ w ∈ candMWit C₁ r_star a b m z_prev x, ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true) ∧
    (∀ w, ∀ (p_edge p_keep : ℝ),
      ∏ i ∈ candQCand C₁ a b m z_prev x w, Sum.elim (fun _ => p_edge) (fun _ => p_keep) i =
        p_keep * p_edge ^ ((candA1 (candMFresh a b m z_prev x)).card +
          (candA2 C₁ a b x (candMFresh a b m z_prev x) w).card)) := by sorry
