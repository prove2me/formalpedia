-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Glue_thm_1_3_from_modules
-- name    : HighDimSteinerSpanners.Proofs.Glue.thm_1_3_from_modules
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:04.592009+00:00
-- url     : https://prove2.me/theorems/9499b3db-ec6d-470e-b09d-ddcc779888d5
-- title:
--   Glue: thm 1 3 from modules
-- statement:
--   Zero-`sorry` derivation of Theorem 1.3
--   (`thm_1_3_non_metric_steiner_spanner_lower_bound`) from Modules 1–3 (`thm_2_1b`,
--   `thm_2_2a`, `thm_2_3`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean#L352-L602
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean#L352-L602

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Glue

theorem HighDimSteinerSpanners.Proofs.Glue.thm_1_3_from_modules
    (h21b : ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)))
    (h22a : ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet)
    (h23 : ∃ M_L : ℝ, 0 < M_L ∧
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
              ListHitCond C₁ rStar X L_X) :
    ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) := by sorry
