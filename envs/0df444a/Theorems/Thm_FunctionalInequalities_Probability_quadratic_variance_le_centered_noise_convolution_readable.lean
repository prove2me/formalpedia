-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_quadratic_variance_le_centered_noise_convolution_readable
-- name    : FunctionalInequalities.Probability.quadratic_variance_le_centered_noise_convolution_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:23.174698+00:00
-- url     : https://prove2.me/theorems/36dbece0-39c9-42e4-832b-b29a213eec41
-- title:
--   Centered Noise Does Not Decrease Quadratic Variance
-- statement:
--   This is a convolution monotonicity statement for quadratic-form variance.
--
--   Let $E$ be a complete real inner-product normed space with Borel and second-countable structure. Let $\mu$ and $\nu$ be probability measures on $E$, each with finite fourth moment, and assume the mean of $\nu$ is zero. For any continuous linear map $A:E\to E$,
--
--   $$\operatorname{Var}_{\mu}\bigl(x\mapsto\langle Ax,x\rangle\bigr)
--   \le \operatorname{Var}_{\mu*\nu}\bigl(x\mapsto\langle Ax,x\rangle\bigr).$$
--
--   Here `Measure.conv` is the law of the sum of independent variables with laws $\mu$ and $\nu$. The result is a reusable variance comparison and does not assert any constant bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 500000 in
--   theorem quadratic_variance_le_centered_noise_convolution
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
--       [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
--       (mu nu : ProbabilityMeasure E)
--       (hmu4 : MemLp (id : E → E) 4 (mu : Measure E))
--       (hnu4 : MemLp (id : E → E) 4 (nu : Measure E))
--       (hmean : (∫ z, z ∂(nu : Measure E)) = 0) (A : E →L[ℝ] E) :
--       variance (fun x : E => ⟪A x, x⟫) (mu : Measure E) ≤
--         variance (fun x : E => ⟪A x, x⟫) ((mu : Measure E).conv (nu : Measure E))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/QuadraticVariance`](https://prove2.me/theorems/8f374ce2-317b-44db-96d6-94eef9130b1f).
--
--   Supporting theorems: [`memLp_quadratic_of_memLp_four`](https://prove2.me/theorems/80afcd22-0f06-48b5-88c9-0fb875897eef), [`decomposition`](https://prove2.me/theorems/dd1a36d4-772f-45aa-a604-8df257afcfb1).
--
--   Previous: [`tendsto_variance_quadratic_matrix_forms`](https://prove2.me/theorems/6bac75bd-e0cf-4ff6-8155-e85bb3d798fc).
--
--   [Source excerpt, lines 96–105](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean#L96-L105) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean#L96-L159 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticVariance`, declaration `FunctionalInequalities.Probability.quadratic_variance_le_centered_noise_convolution`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option maxHeartbeats 500000

theorem FunctionalInequalities.Probability.quadratic_variance_le_centered_noise_convolution_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (mu nu : ProbabilityMeasure E)
    (hmu4 : MemLp (id : E → E) 4 (mu : Measure E))
    (hnu4 : MemLp (id : E → E) 4 (nu : Measure E))
    (hmean : (∫ z, z ∂(nu : Measure E)) = 0) (A : E →L[ℝ] E) :
    variance (fun x : E => ⟪A x, x⟫) (mu : Measure E) ≤
      variance (fun x : E => ⟪A x, x⟫) ((mu : Measure E).conv (nu : Measure E)) := by sorry
