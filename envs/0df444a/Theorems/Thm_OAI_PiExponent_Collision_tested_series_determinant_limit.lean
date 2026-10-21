-- Prove2me | Theorems.Thm_OAI_PiExponent_Collision_tested_series_determinant_limit
-- name    : OAI.PiExponent.Collision.tested_series_determinant_limit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T18:25:34.482561+00:00
-- url     : https://prove2.me/theorems/728a196b-965f-4083-9db3-dec430e53a91
-- title:
--   Determinant bound passes through tested series limits
-- statement:
--   If every finite partial-sum matrix has determinant norm at most K and each entry series sums to the corresponding entry of T, then T’s determinant norm is at most K.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.Collision.tested_series_determinant_limit
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ r c, HasSum (fun d => B r d * C (group r) d c) (T r c))
    (K : ℝ)
    (hbound : ∀ N, ‖Matrix.det (fun r c =>
      ∑ d ∈ Finset.range N, B r d * C (group r) d c)‖ ≤ K) :
    ‖T.det‖ ≤ K := by sorry
