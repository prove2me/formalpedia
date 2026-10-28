-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_hsNormSq_conjugatedNoiseOperator_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.sum_hsNormSq_conjugatedNoiseOperator_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:40.465816+00:00
-- url     : https://prove2.me/theorems/9cbd62f1-3843-46f4-9c08-7b3b98e32302
-- title:
--   Hilbert–Schmidt Bound for Conjugated Noise Operators
-- statement:
--   This bounds the total Hilbert–Schmidt size of the conjugated noise operators.
--
--   Let $\mu$ be a compactly supported isotropic log-concave probability measure on $\mathbb{R}^n$, assume `CumulantBoundCompact 2 8`, and let $p=(c,Q)$ have self-adjoint positive-semidefinite $Q$. Then
--
--   $$
--   \sum_{k\in\operatorname{Fin}(n)}
--   \left\|\widetilde H_k\right\|_{\mathrm{HS}}^2
--   \le 8n.
--   $$
--
--   Here the operators are `conjugatedNoiseOperator` and `hsNormSq` denotes the formalized squared Hilbert–Schmidt norm. The statement is a summed operator-norm estimate used in subsequent generator bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1000000 in
--   theorem sum_hsNormSq_conjugatedNoiseOperator_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
--       (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
--       (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
--       ∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k) ≤ 8 * n
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Bound`](https://prove2.me/theorems/aa56646a-429f-4f7a-b76b-db51e21f5aa2).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/BKL/Localization/Energy/Generator`](https://prove2.me/theorems/736f8a3e-ae32-497a-8859-0c6fecc1a72e), [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Supporting theorems: [`stdMatrix_conjugatedNoiseOperator`](https://prove2.me/theorems/f3141ac7-dca0-4168-8847-cc7e72ce9ce4), [`sum_sq_conjugatedNoiseMatrix_mulVec_le`](https://prove2.me/theorems/bd7bc76e-3a86-4f3a-8622-a29d176bc214).
--
--   Next: [`generator_stdTrace_ringInverse_cov_le`](https://prove2.me/theorems/654de5d1-c780-4937-8de4-674da4bed607).
--
--   [Source excerpt, lines 97–101](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean#L97-L101) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean#L97-L146 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound`, declaration `FunctionalInequalities.KLS.BKL.Localization.sum_hsNormSq_conjugatedNoiseOperator_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound

open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.sum_hsNormSq_conjugatedNoiseOperator_le_readable (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    ∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k) ≤ 8 * n := by sorry
