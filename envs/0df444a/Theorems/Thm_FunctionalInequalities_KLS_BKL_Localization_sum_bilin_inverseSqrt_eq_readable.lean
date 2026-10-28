-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_bilin_inverseSqrt_eq_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.sum_bilin_inverseSqrt_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:46.057134+00:00
-- url     : https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43
-- title:
--   Self-Adjoint Trace Rearrangement
-- statement:
--   This is a finite-dimensional trace rearrangement for a self-adjoint operator.
--
--   Let $n\in\mathbb N$, let $B$ be a bilinear form on $\mathbb R^n$ represented on `EuclideanSpace ℝ (Fin n)`, and let $\sigma$ be a continuous linear map on that space. Assume
--
--   $$\langle\sigma u,v\rangle=\langle u,\sigma v\rangle\quad\text{for all }u,v.$$
--
--   Using the standard coordinate vectors $e_k$, one has
--
--   $$\sum_k B(\sigma e_k,\sigma e_k)
--   =\sum_i B(\sigma^2e_i,e_i).$$
--
--   This technical identity allows a quadratic sum involving an inverse square root to be rewritten as a trace-type expression.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_bilin_inverseSqrt_eq (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)
--       (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) :
--       ∑ k, B (σ (EuclideanSpace.single k 1)) (σ (EuclideanSpace.single k 1)) =
--         ∑ i, B (σ (σ (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Previous: [`fderiv_fderiv_fst_dir`](https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789) · Next: [`sum_inner_inverseSqrt_sq`](https://prove2.me/theorems/d2123cde-3328-49c8-bb38-74191da51e4b).
--
--   [Source excerpt, lines 100–104](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L100-L104) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L99-L140 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.sum_bilin_inverseSqrt_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.Localization.sum_bilin_inverseSqrt_eq_readable (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)
    (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) :
    ∑ k, B (σ (EuclideanSpace.single k 1)) (σ (EuclideanSpace.single k 1)) =
      ∑ i, B (σ (σ (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1) := by sorry
