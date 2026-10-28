-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_coordTensor_le_readable
-- name    : FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:56.129993+00:00
-- url     : https://prove2.me/theorems/fe64a874-0aad-495c-87d8-2d0977852b27
-- title:
--   Coordinate Tensor Norm Bound
-- statement:
--   This theorem bounds the coordinate-array norm of a multilinear map in an orthonormal basis.
--
--   Let $E$ be a real inner-product space, let $n,k\in\mathbb N$, let $b$ be an orthonormal basis indexed by $\operatorname{Fin}(n)$, and let $\Phi:E^k\to\mathbb R$ be a continuous $k$-linear map. Then its coordinate tensor satisfies
--
--   $$\|\operatorname{coordTensor}(b,\Phi)\|\le (\sqrt n)^k\,\|\Phi\|.$$
--
--   Here `coordTensor` is the coefficient array obtained by evaluating $\Phi$ on basis vectors, while $\|\Phi\|$ is the continuous multilinear operator norm. The estimate is a dimension-dependent bridge from operator norms to coordinate Hilbert-space norms.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_coordTensor_le {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
--       (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
--       ‖coordTensor b Φ‖ ≤ Real.sqrt n ^ k * ‖Φ‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f).
--
--   Definition modules: [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f).
--
--   Previous: [`apply_eq_sum_coordTensor`](https://prove2.me/theorems/8f695d42-8d17-42ff-8947-34303d3bbf9f).
--
--   [Source excerpt, lines 181–183](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L181-L183) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L180-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coefficients`, declaration `FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_readable {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖coordTensor b Φ‖ ≤ Real.sqrt n ^ k * ‖Φ‖ := by sorry
