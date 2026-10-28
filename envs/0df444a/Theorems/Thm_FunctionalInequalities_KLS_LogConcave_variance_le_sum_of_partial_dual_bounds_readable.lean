-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_variance_le_sum_of_partial_dual_bounds_readable
-- name    : FunctionalInequalities.KLS.LogConcave.variance_le_sum_of_partial_dual_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:56.5768+00:00
-- url     : https://prove2.me/theorems/87d34084-ab4b-4b3e-96bf-c24d3921e663
-- title:
--   Variance Bound From Partial Dual Estimates
-- statement:
--   This formalizes the $H^{-1}$ variance inequality of Letwin (arXiv:2607.24164v1) (Proposition 2.8, partial relation).
--
--   Let $n\in\mathbb N$, let $m$ be an additive Haar measure on $E=\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$, and let $\nu$ be log-concave with
--
--   $$
--   \nu=m.\operatorname{tilted}(-W).
--   $$
--
--   Assume:
--
--   1. $W$ is $C^2$ and convex on all of $E$.
--   2. $f:E\to\mathbb R$ is $C^1$ and belongs to $L^2(\nu)$.
--   3. Every coordinate derivative $x\mapsto Df(x)[e_i]$ belongs to $L^2(\nu)$, where $e_i=\operatorname{single}(i,1)$.
--   4. For each $i$ and every smooth compactly supported $h$,
--      $$
--      \left(\int_E Df(x)[e_i]h(x)\,d\nu(x)\right)^2
--      \le K_i\int_E\|Dh(x)\|^2\,d\nu(x).
--      $$
--
--   Then
--
--   $$
--   \operatorname{Var}_\nu(f)\le\sum_{i=1}^n K_i.
--   $$
--
--   The theorem is finite-dimensional and retains the explicit $C^2$ convexity, $L^2$, and coordinate-derivative hypotheses. It is a variance assembly result from the separate compact-test dual bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem variance_le_sum_of_partial_dual_bounds {n : ℕ}
--       (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
--       {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hν : FunctionalInequalities.KLS.LogConcave ν)
--       {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
--       (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (ν : Measure _))
--       (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (ν : Measure _))
--       (K : Fin n → ℝ)
--       (hK : ∀ i (h : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ ∞ h → HasCompactSupport h →
--         (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure _)) ^ 2 ≤
--           K i * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
--       variance f (ν : Measure _) ≤ ∑ i, K i
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HminusOne`](https://prove2.me/theorems/4dc71c7a-51b5-45a0-8de3-41cf287dbc05).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Selected supporting theorems: [`sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq`](https://prove2.me/theorems/34cc3097-b38d-4f33-9bd3-39c1af8e4e9d), [`centered_mem_closure_compactSmoothDiffusionImage`](https://prove2.me/theorems/cc2ca884-a315-433e-8321-8e49b01e29b4), [`compact_pairing_identity`](https://prove2.me/theorems/77b2a911-3499-4ec7-80ff-b5c0181f947f), [`inner_center_left_of_mean_zero`](https://prove2.me/theorems/eeca0bb8-9f32-4e5c-ba1e-1f7ba9ea09b0), [`nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq`](https://prove2.me/theorems/b98a51cc-c659-42c7-9c41-59b73de13a36).
--
--   Previous: [`sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq`](https://prove2.me/theorems/34cc3097-b38d-4f33-9bd3-39c1af8e4e9d).
--
--   [Source excerpt, lines 456–467](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L456-L467) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Proposition 2.8 (Barthe and Klartag [7, Proposition 10]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L450-L631 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HminusOne`, declaration `FunctionalInequalities.KLS.LogConcave.variance_le_sum_of_partial_dual_bounds`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne

open MeasureTheory
open scoped ContDiff
open ProbabilityTheory InnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.variance_le_sum_of_partial_dual_bounds_readable {n : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hν : FunctionalInequalities.KLS.LogConcave ν)
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
    (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (ν : Measure _))
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (ν : Measure _))
    (K : Fin n → ℝ)
    (hK : ∀ i (h : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure _)) ^ 2 ≤
        K i * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    variance f (ν : Measure _) ≤ ∑ i, K i := by sorry
