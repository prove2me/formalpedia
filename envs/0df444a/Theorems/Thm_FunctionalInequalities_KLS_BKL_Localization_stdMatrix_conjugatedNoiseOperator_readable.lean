-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_stdMatrix_conjugatedNoiseOperator_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.stdMatrix_conjugatedNoiseOperator_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:11.589383+00:00
-- url     : https://prove2.me/theorems/f3141ac7-dca0-4168-8847-cc7e72ce9ce4
-- title:
--   Matrix Representation of the Conjugated Noise Operator
-- statement:
--   This identifies the coordinate matrix of each conjugated noise operator.
--
--   Let $\mu$ be a compactly supported isotropic probability measure on $\mathbb{R}^n$. For a localization parameter $p$ and $k\in\operatorname{Fin}(n)$, let $P=A(p)^{-1/2}$ and $H_k=D_cA(p)[\operatorname{noise}(\mu,p,k)]$. Then the standard matrix of the operator $P H_k P$ is the matrix whose entries are
--
--   $$
--   \bigl[\widetilde H_k\bigr]_{ab}
--   =\kappa_3(\mu_p)(P e_a,P e_b,P e_k).
--   $$
--
--   In the formal statement this is `stdMatrix (conjugatedNoiseOperator μ hc p k) = conjugatedNoiseMatrix μ hc p k`. It supplies the coordinate form needed for Hilbert–Schmidt and vector norm estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1000000 in
--   theorem stdMatrix_conjugatedNoiseOperator (hiso : KLS.Isotropic μ)
--       (p : Param n) (k : Fin n) :
--       stdMatrix (conjugatedNoiseOperator μ hc p k) =
--         conjugatedNoiseMatrix μ hc p k
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Generator`](https://prove2.me/theorems/736f8a3e-ae32-497a-8859-0c6fecc1a72e).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72), [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Supporting theorems: [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`fderiv_cumulant_posterior_apply`](https://prove2.me/theorems/7e33f35a-71f2-43a6-bb75-a119f0e67849), [`inner_cov_apply`](https://prove2.me/theorems/9dacc562-afff-4880-8959-c09a4a246ec3), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   Next: [`generator_cumulantEnergy_eq`](https://prove2.me/theorems/6cd32b47-947e-4f45-b7b2-d7005d995bc0).
--
--   [Source excerpt, lines 186–190](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L186-L190) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L186-L230 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Generator`, declaration `FunctionalInequalities.KLS.BKL.Localization.stdMatrix_conjugatedNoiseOperator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator

open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.stdMatrix_conjugatedNoiseOperator_readable (hiso : KLS.Isotropic μ)
    (p : Param n) (k : Fin n) :
    stdMatrix (conjugatedNoiseOperator μ hc p k) =
      conjugatedNoiseMatrix μ hc p k := by sorry
