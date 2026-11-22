-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_thm_2_3_from_6_3
-- name    : HighDimSteinerSpanners.Proofs.CSP.thm_2_3_from_6_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:39.434051+00:00
-- url     : https://prove2.me/theorems/61a19526-c6aa-4528-a134-8b15a90b436a
-- title:
--   CSP: thm 2 3 from 6 3
-- statement:
--   **Theorem 2.3 (Existence of Locally List-Bounded `2`-CSP Codes, Module 3)** Takes Lemma
--   6.3 (`h_6_3`) as an explicit hypothesis so this module compiles independently.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP.lean#L31-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP.lean#L31-L241

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Existence
public import Definitions.Def_LeanPool_SteinerSpanners_CSP
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP

theorem HighDimSteinerSpanners.Proofs.CSP.thm_2_3_from_6_3
    (h_6_3 : ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X) :
    ∃ M_L : ℝ, 0 < M_L ∧
      ∀ C₁ : ℕ, 3 ≤ C₁ →
        ∃ (L q K R₀ : ℕ) (μ₀ : ℝ),
          2 ≤ L ∧ (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ∧
          2 ≤ q ∧ K = 20 * C₁ ^ 2 ∧ 160 * C₁ < R₀ ∧ 0 < μ₀ ∧
          let c : ℝ := (2 : ℝ) ^ (-((2 * L + 5 : ℕ) : ℝ))
          ∀ rStar : ℕ, R₀ ≤ rStar →
            let N : ℕ := 2 ^ L * rStar
            ∃ (X : Finset (Fin N → Fin q)) (L_X : ↥X → ↥X → Finset ↥X),
              2 ≤ X.card ∧
              (2 : ℝ) / 5 * μ₀ * (rStar : ℝ) ≤ Real.logb 2 (X.card : ℝ) ∧
              Real.logb 2 (X.card : ℝ) ≤ (3 : ℝ) / 2 * μ₀ * (rStar : ℝ) ∧
              (1 : ℝ) / 192 * (X.card : ℝ) ^ (1 + c) ≤ ((exactDistPairs X rStar).card : ℝ) ∧
              (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) ∧
              ListSizeCond C₁ rStar K X L_X ∧
              OverlapCond C₁ rStar K X ∧
              ListHitCond C₁ rStar X L_X := by sorry
