-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_complete_graph_2csp_expurgated_existence
-- name    : HighDimSteinerSpanners.Proofs.CSP.complete_graph_2csp_expurgated_existence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:16.259798+00:00
-- url     : https://prove2.me/theorems/1150cc6e-3253-48cc-a4d0-6986deb915ff
-- title:
--   CSP: complete graph 2csp expurgated existence
-- statement:
--   The CSP construction uses the complete graph 2csp expurgated existence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Existence.lean#L1844-L2000
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Existence.lean#L1844-L2000

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_ClosePairs
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Existence
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.complete_graph_2csp_expurgated_existence (C₁ : ℕ) (hC₁ : 3 ≤ C₁)
    (r_star : ℕ) (hr : 1000 * C₁ < r_star) :
    ∃ (R : Fin (2 ^ cspL C₁ * r_star) → Fin (2 ^ cspL C₁ * r_star) →
          Fin (cspQ C₁) → Fin (cspQ C₁) → Prop)
      (X_set : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))),
      Symmetric2CSP R ∧
      X_set ⊆ satisfyingSet R ∧
      ((2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (X_set.card : ℝ) ∧
       (X_set.card : ℝ) ≤
        (2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ))) ∧
      ((2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) * (X_set.card : ℝ) ≤
        192 * (((X_set ×ˢ X_set).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ)) ∧
      (∀ x ∈ X_set, ∀ u ∈ X_set, ∀ z ∈ satisfyingSet R,
        dHam x u ≤ C₁ * r_star → dHam x z ≤ C₁ * r_star →
        cspInvEta0 C₁ * (threeWayDisagree x u z).card ≤ r_star) ∧
      (∀ x ∈ X_set, ∀ w₀ ∈ X_set, x ≠ w₀ → dHam x w₀ ≤ C₁ * r_star →
        (X_set.filter (fun y =>
          y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
          r_star < 4 * (disagreeSet x w₀ ∩ disagreeSet x y).card)).card < cspKCh C₁) ∧
      (∀ a ∈ X_set, ∀ b ∈ X_set, a ≠ b → dHam a b ≤ C₁ * r_star →
        (X_set.filter (fun x => x ∈ bicliqueWitnessList R C₁ r_star a b)).card < cspKMom C₁) ∧
      (∀ x ∈ X_set, ∀ y ∈ X_set, x ≠ y → r_star ≤ 2 * dHam x y) := by sorry
