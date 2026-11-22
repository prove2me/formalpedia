-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Dvoretzky_cor_1_4_from_1_3
-- name    : HighDimSteinerSpanners.Proofs.Dvoretzky.cor_1_4_from_1_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:37.866421+00:00
-- url     : https://prove2.me/theorems/40e5b040-ec7f-4d1f-8c36-241762771fac
-- title:
--   Dvoretzky: cor 1 4 from 1 3
-- statement:
--   **Corollary 1.4 (`p`-Independent Exponent for `p > 2` via Dvoretzky Embedding)** Takes
--   `lpDist_eq_toLp_dist` and Theorem 1.3 as explicit hypotheses so this module compiles
--   independently.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Dvoretzky.lean#L1476-L1711
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Dvoretzky.lean#L1476-L1711

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Dvoretzky
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Dvoretzky

theorem HighDimSteinerSpanners.Proofs.Dvoretzky.cor_1_4_from_1_3
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    (h_1_3 : ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
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
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ)) :
    ∃ (M : ℝ) (c c₀ A : ℝ → ℝ),
      0 < M ∧
      (∀ C : ℝ, 1 ≤ C →
        (2 : ℝ) ^ (-M * C ^ (6 : ℕ) * Real.logb 2 (C + 1)) ≤ c C ∧ 0 < c₀ C ∧ 0 < A C) ∧
      ∀ (p : ℝ), 2 < p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (β₁ β₂ : ℝ), 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A C ∧
                  (∀ (S : Type) [Fintype S]
                    (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                    (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                    IsNonMetricSteinerSpanner p P C H w →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ)) ∧
                  (∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card G.edgeSet : ℝ)) := by sorry
