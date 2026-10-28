-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_compact_pairing_identity_readable
-- name    : FunctionalInequalities.KLS.LogConcave.compact_pairing_identity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:47.052822+00:00
-- url     : https://prove2.me/theorems/77b2a911-3499-4ec7-80ff-b5c0181f947f
-- title:
--   Compact Diffusion Pairing Identity
-- statement:
--   This theorem gives the integration-by-parts identity for a compactly supported diffusion test.
--
--   Let $E$ be finite-dimensional with its real inner-product structure, let $m$ be an additive Haar measure, let $\nu$ be a probability measure, and let $U:E\to\mathbb R$ satisfy $\nu=m.\operatorname{tilted}(-U)$. Assume $U$ and $f$ are $C^1$, while $u:E\to\mathbb R$ is $C^\infty$ and compactly supported. Then both functions
--
--   $$
--   f(x)\,[-\mathcal L_Uu(x)]
--   \quad\text{and}\quad
--   \langle\nabla f(x),\nabla u(x)\rangle
--   $$
--
--   are integrable with respect to $\nu$, and
--
--   $$
--   \int_E f(x)\,[-\mathcal L_Uu(x)]\,d\nu(x)
--   =
--   \int_E \langle\nabla f(x),\nabla u(x)\rangle\,d\nu(x),
--   $$
--
--   where `weightedLaplacian` denotes $\mathcal L_U$. The function $f$ need not be compactly supported.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compact_pairing_identity
--       {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
--       {U f u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
--       (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 1 f)
--       (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
--       Integrable (fun x => f x * (-weightedLaplacian U u x)) (ν : Measure E) ∧
--         Integrable (fun x => ⟪gradient f x, gradient u x⟫) (ν : Measure E) ∧
--         (∫ x, f x * (-weightedLaplacian U u x) ∂(ν : Measure E)) =
--           ∫ x, ⟪gradient f x, gradient u x⟫ ∂(ν : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BrascampLieb`](https://prove2.me/theorems/ef0b3d78-2213-4c3c-ab7c-7dd44bfe1cfb).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Previous: [`inner_center_left_of_mean_zero`](https://prove2.me/theorems/eeca0bb8-9f32-4e5c-ba1e-1f7ba9ea09b0).
--
--   [Source excerpt, lines 105–113](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean#L105-L113) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean#L103-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BrascampLieb`, declaration `FunctionalInequalities.KLS.LogConcave.compact_pairing_identity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb

open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem FunctionalInequalities.KLS.LogConcave.compact_pairing_identity_readable
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U f u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 1 f)
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    Integrable (fun x => f x * (-weightedLaplacian U u x)) (ν : Measure E) ∧
      Integrable (fun x => ⟪gradient f x, gradient u x⟫) (ν : Measure E) ∧
      (∫ x, f x * (-weightedLaplacian U u x) ∂(ν : Measure E)) =
        ∫ x, ⟪gradient f x, gradient u x⟫ ∂(ν : Measure E) := by sorry
