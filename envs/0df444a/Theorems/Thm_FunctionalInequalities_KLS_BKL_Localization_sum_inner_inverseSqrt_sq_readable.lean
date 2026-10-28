-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_inner_inverseSqrt_sq_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.sum_inner_inverseSqrt_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:05.026541+00:00
-- url     : https://prove2.me/theorems/d2123cde-3328-49c8-bb38-74191da51e4b
-- title:
--   Self-Adjoint Coordinate Expansion
-- statement:
--   This is the coordinate expansion of a quadratic form for a self-adjoint operator.
--
--   Let $\sigma:\mathbb{R}^n\to\mathbb{R}^n$ be a continuous linear map satisfying
--
--   $$
--   \langle\sigma u,v\rangle=\langle u,\sigma v\rangle
--   $$
--
--   for all $u,v\in\mathbb{R}^n$. Then, for every $v\in\mathbb{R}^n$,
--
--   $$
--   \sum_k\langle\sigma e_k,v\rangle^2
--   =\langle v,\sigma(\sigma v)\rangle,
--   $$
--
--   where $e_k$ are the Euclidean coordinate basis vectors. This elementary identity is used to rewrite sums involving the inverse square root of a covariance operator.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_inner_inverseSqrt_sq (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) (v : EuclideanSpace ℝ (Fin n)) :
--       ∑ k, ⟪σ (EuclideanSpace.single k 1), v⟫ * ⟪σ (EuclideanSpace.single k 1), v⟫ =
--         ⟪v, σ (σ v)⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Previous: [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43) · Next: [`generator_posteriorExpectation_exp_inner`](https://prove2.me/theorems/6a6bdaa6-0ece-4bfe-854e-2c005a8cead7).
--
--   [Source excerpt, lines 143–146](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L143-L146) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L142-L158 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.sum_inner_inverseSqrt_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.Localization.sum_inner_inverseSqrt_sq_readable (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) (v : EuclideanSpace ℝ (Fin n)) :
    ∑ k, ⟪σ (EuclideanSpace.single k 1), v⟫ * ⟪σ (EuclideanSpace.single k 1), v⟫ =
      ⟪v, σ (σ v)⟫ := by sorry
