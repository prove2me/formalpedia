-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulantEnergy_ge_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_ge_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:45.524988+00:00
-- url     : https://prove2.me/theorems/d995a803-9dc2-4144-b611-6d14e68dd120
-- title:
--   Cumulant Energy Generator Lower Bound
-- statement:
--   This formalizes the generator form of BKL Lemma 5.1, equation (80), cited at p. 22 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be an isotropic, compactly supported, log-concave probability measure on $\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$. Assume the compact cumulant bound `CumulantBoundCompact 2 8`. Let $r\ge2$, let $u$ be a direction, and let $p=(c,Q)$ be a localization parameter. Assume $Q$ is self-adjoint and positive semidefinite: $\langle Qx,x\rangle\ge0$ for every $x$.
--
--   Writing $E_r=\operatorname{cumulantEnergy}(\mu_p,r,u)$ and $L_r$ for the displayed lower-drift pairing, the conclusion is
--
--   $$
--   \frac12E_{r+1}-17(r+1)^2E_r-2L_r
--   \le \mathcal L_p E_r.
--   $$
--
--   More explicitly, $L_r$ is the finite sum over $K:\mathrm{Fin}(r)\to\mathrm{Fin}(n)$ of the $(r+1)$st cumulant evaluated on $u$ and the whitened basis directions, multiplied by `lowerDrift` at slot $0$. This is a quantitative auxiliary inequality with the explicit constant $17$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_cumulantEnergy_ge (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
--       (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℕ} (hr : 2 ≤ r)
--       (u : EuclideanSpace ℝ (Fin n)) (p : Param n) (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
--       (1 / 2 : ℝ) * cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1) u
--           - 17 * ((r : ℝ) + 1) ^ 2 *
--             cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) r u
--           - 2 * ∑ K : Fin r → Fin n,
--               cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
--                   (Fin.cons u fun s => inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
--                 lowerDrift (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
--                   (Fin.cons u fun s => inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ≤
--         generator μ hc
--           (fun q : Param n => cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Generator`](https://prove2.me/theorems/736f8a3e-ae32-497a-8859-0c6fecc1a72e).
--
--   Definition modules: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Selected supporting theorems: [`contDiffAt_energyForm`](https://prove2.me/theorems/3ecc6a67-dc0c-4de0-aced-f227c0a5133b), [`deriv_deriv_energyForm_line`](https://prove2.me/theorems/8ec8d6e9-231a-4f63-b067-a5beeb835aaf), [`drift_expression_ge`](https://prove2.me/theorems/a395a5ad-1152-4611-ab50-eae8318965ce), [`fderiv_fderiv_apply_eq_deriv_deriv_line`](https://prove2.me/theorems/91499aa3-4a30-4b4f-af4c-05085add7997), [`hasDerivAt_energyForm_line`](https://prove2.me/theorems/7d3fc6e6-7635-41c8-9e97-877316e76ce3).
--
--   Previous: [`generator_cumulantEnergy_eq`](https://prove2.me/theorems/6cd32b47-947e-4f45-b7b2-d7005d995bc0).
--
--   [Source excerpt, lines 497–509](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L497-L509) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 5.1, p. 22. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L490-L632 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Generator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_ge`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
open scoped RealInnerProductSpace
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_ge_readable (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (p : Param n) (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    (1 / 2 : ℝ) * cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1) u
        - 17 * ((r : ℝ) + 1) ^ 2 *
          cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) r u
        - 2 * ∑ K : Fin r → Fin n,
            cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
                (Fin.cons u fun s => inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
              lowerDrift (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
                (Fin.cons u fun s => inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ≤
      generator μ hc
        (fun q : Param n => cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p := by sorry
