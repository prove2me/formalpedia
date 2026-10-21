-- Prove2me | Theorems.Thm_OAI_PiExponent_Collision_infinite_tested_series_collision_bound
-- name    : OAI.PiExponent.Collision.infinite_tested_series_collision_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T18:07:44.424562+00:00
-- url     : https://prove2.me/theorems/b817576a-61bf-4c1e-a954-65bab578a6d4
-- title:
--   Collision estimate for determinants of geometrically tested series
-- statement:
--   For D,L nonnegative and 0≤s<1, a matrix represented by group-dependent bounded coefficients and row factors bounded by L(r)s^(2d) satisfies a determinant estimate with factorial, coefficient, row-cost, same-group collision, and geometric-tail factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.Collision.infinite_tested_series_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ r, 0 ≤ L r)
    (hC : ∀ A d c, ‖C A d c‖ ≤ D)
    (hB : ∀ r d, ‖B r d‖ ≤ L r * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ r c, HasSum (fun d => B r d * C (group r) d c) (T r c)) :
    ‖T.det‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι * (∏ r, L r)) *
        s ^ (∑ A : κ, (((Finset.univ : Finset ι).filter
          (fun r => group r = A)).card.choose 2)) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by sorry
