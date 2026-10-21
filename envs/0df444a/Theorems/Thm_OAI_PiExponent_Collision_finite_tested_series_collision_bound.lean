-- Prove2me | Theorems.Thm_OAI_PiExponent_Collision_finite_tested_series_collision_bound
-- name    : OAI.PiExponent.Collision.finite_tested_series_collision_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T18:25:24.995193+00:00
-- url     : https://prove2.me/theorems/ae12e92f-e89b-4e62-b1a1-ca7690b4f4bd
-- title:
--   Finite truncation collision estimate
-- statement:
--   For every finite cutoff N, the determinant of the matrix formed from degrees d<N obeys the collision estimate under the target coefficient and parameter bounds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.Collision.finite_tested_series_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ r, 0 ≤ L r)
    (hC : ∀ A d c, ‖C A d c‖ ≤ D)
    (hB : ∀ r d, ‖B r d‖ ≤ L r * (s * s) ^ d) :
    ‖Matrix.det (fun r c => ∑ d ∈ Finset.range N, B r d * C (group r) d c)‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι * (∏ r, L r)) *
        s ^ (∑ A : κ, (((Finset.univ : Finset ι).filter
          (fun r => group r = A)).card.choose 2)) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by sorry
