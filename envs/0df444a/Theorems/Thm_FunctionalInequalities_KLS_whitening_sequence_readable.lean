-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_whitening_sequence_readable
-- name    : FunctionalInequalities.KLS.whitening_sequence_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:17.158073+00:00
-- url     : https://prove2.me/theorems/4f39d579-4312-46d4-8a78-c4f9ba76eab9
-- title:
--   Asymptotically Whitening Positive Operators
-- statement:
--   This auxiliary lemma constructs an asymptotically identity whitening sequence.
--
--   Let $E$ be a finite-dimensional real inner-product space, and let $C_k:E\to E$ be continuous linear maps. Assume each $C_k$ is positive and that $C_k\to I$ in the operator topology. Then there exists a sequence of continuous linear equivalences $L_k:E\simeq_L E$ such that:
--
--   1. $L_k\to I$ in the operator topology;
--   2. for all sufficiently large $k$, $L_k$ is self-adjoint and satisfies
--
--   $$
--   L_k\,C_k\,L_k=I.
--   $$
--
--   The statement provides the whitening operators used in the approximation construction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma whitening_sequence (C : ℕ → E →L[ℝ] E)
--       (hpos : ∀ k, (C k).IsPositive) (hC : Tendsto C atTop (𝓝 1)) :
--       ∃ L : ℕ → E ≃L[ℝ] E,
--         Tendsto (fun k => (L k).toContinuousLinearMap) atTop (𝓝 1) ∧
--         ∀ᶠ k in atTop,
--           IsSelfAdjoint (L k).toContinuousLinearMap ∧
--           (L k).toContinuousLinearMap * C k * (L k).toContinuousLinearMap = 1
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BallConditioning`](https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc).
--
--   Supporting theorems: [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a).
--
--   Previous: [`covariance_tendsto_one`](https://prove2.me/theorems/931a2bcc-f8c0-48ee-8d9a-a38753c18c36) · Next: [`exists_whitening_tendsto_moments`](https://prove2.me/theorems/e2bcc388-90fd-4d11-8bef-4995ad9590a2).
--
--   [Source excerpt, lines 373–379](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L373-L379) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L373-L455 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BallConditioning`, declaration `_private.FunctionalInequalities.KLS.LogConcave.BallConditioning.0.FunctionalInequalities.KLS.whitening_sequence`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning

open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma FunctionalInequalities.KLS.whitening_sequence_readable (C : ℕ → E →L[ℝ] E)
    (hpos : ∀ k, (C k).IsPositive) (hC : Tendsto C atTop (𝓝 1)) :
    ∃ L : ℕ → E ≃L[ℝ] E,
      Tendsto (fun k => (L k).toContinuousLinearMap) atTop (𝓝 1) ∧
      ∀ᶠ k in atTop,
        IsSelfAdjoint (L k).toContinuousLinearMap ∧
        (L k).toContinuousLinearMap * C k * (L k).toContinuousLinearMap = 1 := by sorry
