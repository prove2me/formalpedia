-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_abs_laplacian_le_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.abs_laplacian_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:52.543382+00:00
-- url     : https://prove2.me/theorems/f6e58a8e-3f46-421d-a064-a1f1705fd429
-- title:
--   Laplacian Bound by the Hessian Norm
-- statement:
--   This is a pointwise finite-dimensional estimate for the scalar Laplacian.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $g:E\to\mathbb R$ be any function, and let $x\in E$. No differentiability or completeness hypothesis on $g$ is assumed.
--
--   $$
--   |\Delta g(x)|\leq \dim(E)\,\|D^2g(x)\|.
--   $$
--
--   Here $D^2g(x)$ is represented by `iteratedFDeriv ℝ 2 g x`, and $\dim(E)$ is the real vector-space dimension. The estimate is obtained using the fixed standard orthonormal basis and is valid also in dimension zero.
--
--   **Formalization Note** The norm and inequality are real-valued; no measure-theoretic assumptions occur.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_laplacian_le (g : E → ℝ) (x : E) :
--       |Laplacian.laplacian g x| ≤ Module.finrank ℝ E * ‖iteratedFDeriv ℝ 2 g x‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Temperate`](https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca).
--
--   Previous: [`norm_iteratedFDeriv_cutoff_le`](https://prove2.me/theorems/d1de012f-6a55-4617-aaf5-23eabb181c3e) · Next: [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db).
--
--   [Source excerpt, lines 179–180](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L179-L180) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L177-L205 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.abs_laplacian_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.abs_laplacian_le_readable (g : E → ℝ) (x : E) :
    |Laplacian.laplacian g x| ≤ Module.finrank ℝ E * ‖iteratedFDeriv ℝ 2 g x‖ := by sorry
