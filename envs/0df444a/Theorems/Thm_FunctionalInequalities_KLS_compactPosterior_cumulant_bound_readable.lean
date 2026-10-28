-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_compactPosterior_cumulant_bound_readable
-- name    : FunctionalInequalities.KLS.compactPosterior_cumulant_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:22.434718+00:00
-- url     : https://prove2.me/theorems/dafbeb46-ce93-4b8d-bf8b-6a64738b3ea3
-- title:
--   Standardized Compact Posterior Cumulant Bound
-- statement:
--   This formalizes the standardized posterior cumulant estimate associated with Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited there as an alternative formulation of the cumulant bounds.
--
--   Work in $E=\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$. Let $\mu$ be a compactly supported isotropic log-concave probability law. Let $c\in E$ and let $Q:E\to E$ be self-adjoint and positive semidefinite. Put
--
--   $$
--   \pi=\mu_{c,Q},\qquad A=\operatorname{Cov}(\pi),\qquad \sigma=A^{-1/2}.
--   $$
--
--   Assume $d\ge1$, assume `CumulantBoundCompact d b`, and let $v\in E$. Then
--
--   $$
--   \sum_{J:\operatorname{Fin}d\to\operatorname{Fin}n}
--   \kappa_{d+1}\bigl(\pi;v,\sigma e_{J_1},\ldots,\sigma e_{J_d}\bigr)^2
--   \le b\,\langle Av,v\rangle,
--   $$
--
--   where $(e_j)$ is the standard orthonormal basis and $\kappa_{d+1}$ is `cumulant` of the posterior measure.
--
--   The result transfers a compact cumulant bound for the standardized posterior back to the original posterior, with the covariance quadratic form on the right-hand side. It is stated in every finite dimension, including $n=0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compactPosterior_cumulant_bound {n : ℕ}
--       (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
--       (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
--       (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
--       {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : LogConcave.Suspension.CumulantBoundCompact d b)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       ∑ J : Fin d → Fin n,
--           cumulant (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
--             (Fin.cons v fun k => inverseSqrt (Covariance.operator
--               (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
--                 (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2 ≤
--         b * ⟪Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Standardization`](https://prove2.me/theorems/d6ac7b3b-4286-4c25-abe4-12ef241d0c20).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Selected supporting theorems: [`cumulant_map_affine`](https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b), [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`Isotropic.exists_inverseSqrt_equiv_isotropic_standardized`](https://prove2.me/theorems/590c5914-bf1c-477c-b78a-cf7e5e57e017), [`logConcave_of_concave_tilt`](https://prove2.me/theorems/ec28e166-3e80-4482-a015-77d8598725bc).
--
--   [Source excerpt, lines 26–39](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Standardization.lean#L26-L39) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Standardization.lean#L21-L188 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Standardization`, declaration `FunctionalInequalities.KLS.compactPosterior_cumulant_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Standardization

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.compactPosterior_cumulant_bound_readable {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
    {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : LogConcave.Suspension.CumulantBoundCompact d b)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∑ J : Fin d → Fin n,
        cumulant (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons v fun k => inverseSqrt (Covariance.operator
            (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2 ≤
      b * ⟪Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by sorry
