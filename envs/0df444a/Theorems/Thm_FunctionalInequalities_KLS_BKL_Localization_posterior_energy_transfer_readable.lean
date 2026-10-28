-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_posterior_energy_transfer_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.posterior_energy_transfer_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:49.899203+00:00
-- url     : https://prove2.me/theorems/d67b027d-a7b5-4e5f-9323-596964225290
-- title:
--   Transfer of Cumulant Energy Through Standardization
-- statement:
--   This auxiliary statement transfers an isotropic cumulant bound to a compact posterior.
--
--   Let $\mu$ be a compactly supported isotropic log-concave probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$. Let $c\in E$ and let $Q$ be self-adjoint and positive semidefinite. Assume $d\ge1$ and suppose that every compactly supported isotropic log-concave law satisfies
--
--   $$
--   \sum_J\kappa_{d+1}(\nu;u,e_{J_1},\ldots,e_{J_d})^2
--   \le b\|u\|^2.
--   $$
--
--   Then every $v\in E$ satisfies
--
--   $$
--   \operatorname{cumulantEnergy}(\mu_{c,Q},d,v)
--   \le b\,\langle\operatorname{Cov}(\mu_{c,Q})v,v\rangle.
--   $$
--
--   This is a technical transport lemma and does not itself provide the assumed constant $b$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem posterior_energy_transfer
--       (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
--       (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
--       (c : EuclideanSpace ℝ (Fin n))
--       (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
--       {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
--       (h : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
--         KLS.LogConcave ν → KLS.Isotropic ν →
--         IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
--         ∀ u : EuclideanSpace ℝ (Fin n),
--           ∑ J : Fin d → Fin n,
--             cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
--               (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
--             b * ‖u‖ ^ 2)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       cumulantEnergy (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) d v ≤
--         b * ⟪Covariance.operator
--           (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Bound`](https://prove2.me/theorems/4ab05ed1-3d8d-48ff-a6a8-e41faa7f3068).
--
--   Definition modules: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Selected supporting theorems: [`cumulant_map_affine`](https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b), [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`Isotropic.exists_inverseSqrt_equiv_isotropic_standardized`](https://prove2.me/theorems/590c5914-bf1c-477c-b78a-cf7e5e57e017), [`logConcave_of_concave_tilt`](https://prove2.me/theorems/ec28e166-3e80-4482-a015-77d8598725bc).
--
--   Next: [`norm_posteriorMean_le`](https://prove2.me/theorems/1ba79c02-44ff-4be0-ac9c-b3cb262c225b).
--
--   [Source excerpt, lines 24–43](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean#L24-L43) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean#L24-L167 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Bound`, declaration `_private.FunctionalInequalities.KLS.BKL.Localization.Energy.Bound.0.FunctionalInequalities.KLS.BKL.Localization.posterior_energy_transfer`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.Localization.posterior_energy_transfer_readable
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
    {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (h : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      KLS.LogConcave ν → KLS.Isotropic ν →
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∑ J : Fin d → Fin n,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
          b * ‖u‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) d v ≤
      b * ⟪Covariance.operator
        (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by sorry
