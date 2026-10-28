-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulantEnergy_eq_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:08.56241+00:00
-- url     : https://prove2.me/theorems/6cd32b47-947e-4f45-b7b2-d7005d995bc0
-- title:
--   Cumulant Energy Generator Chain Rule
-- statement:
--   This is the chain-rule expression for the generator of the posterior cumulant energy.
--
--   Let $\mu$ be an isotropic probability measure on $\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ with compact support. Let $r\in\mathbb N$ satisfy $2\le r$, let $u$ be a direction, and let $p=(c,Q)$ be a localization parameter. Define $E_r(p,u)=\operatorname{cumulantEnergy}(\mu_p,r,u)$, and write `energyForm` for the quadratic form applied to the covariance-coordinate tensor and cumulant tensor. The identity uses `energyTensor`, `lowerTensor`, `noiseTensor`, and `conjugatedNoiseOperator`.
--
--   $$
--   \mathcal L E_r(p,u)=D\!F(1,E_r^{\mathrm{tensor}})\bigl[-1,-((r+1)E_r^{\mathrm{tensor}}+L_r^{\mathrm{tensor}})\bigr]
--   +\frac12\sum_kD^2F(1,E_r^{\mathrm{tensor}})[(\widetilde H_k,W_k),(\widetilde H_k,W_k)] .
--   $$
--
--   The equality is a technical generator decomposition in conjugated coordinates. It isolates the drift and noise derivatives needed for subsequent energy inequalities; it does not itself assert a lower bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1000000 in
--   theorem generator_cumulantEnergy_eq (hiso : KLS.Isotropic μ) {r : ℕ} (hr : 2 ≤ r)
--       (u : EuclideanSpace ℝ (Fin n)) (p : Param n) :
--       generator μ hc
--           (fun q : Param n => cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p =
--         fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
--             energyForm q.1 q.2) (1, energyTensor μ hc p r u)
--             (-1, -(((r : ℝ) + 1) • energyTensor μ hc p r u + lowerTensor μ hc p r u)) +
--           (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ
--             (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
--               energyForm q.1 q.2)) (1, energyTensor μ hc p r u)
--             (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k)
--             (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Generator`](https://prove2.me/theorems/736f8a3e-ae32-497a-8859-0c6fecc1a72e).
--
--   Definition modules: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Selected supporting theorems: [`contDiffAt_energyForm`](https://prove2.me/theorems/3ecc6a67-dc0c-4de0-aced-f227c0a5133b), [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`contDiff_cumulant_posterior`](https://prove2.me/theorems/fae38448-b47c-4a2d-b61a-67ba2745ecc0).
--
--   Previous: [`stdMatrix_conjugatedNoiseOperator`](https://prove2.me/theorems/f3141ac7-dca0-4168-8847-cc7e72ce9ce4) · Next: [`generator_cumulantEnergy_ge`](https://prove2.me/theorems/d995a803-9dc2-4144-b611-6d14e68dd120).
--
--   [Source excerpt, lines 251–263](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L251-L263) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L251-L407 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Generator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_eq_readable (hiso : KLS.Isotropic μ) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (p : Param n) :
    generator μ hc
        (fun q : Param n => cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p =
      fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
          energyForm q.1 q.2) (1, energyTensor μ hc p r u)
          (-1, -(((r : ℝ) + 1) • energyTensor μ hc p r u + lowerTensor μ hc p r u)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ
          (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
            energyForm q.1 q.2)) (1, energyTensor μ hc p r u)
          (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k)
          (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k) := by sorry
