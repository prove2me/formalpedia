-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_norm_gradient_scaled_mul_sq_le_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:27.792775+00:00
-- url     : https://prove2.me/theorems/1194b2a8-bd6e-4efd-bc86-f6b48715f7e0
-- title:
--   Squared Gradient Bound for a Scaled Cutoff Product
-- statement:
--   This is a pointwise estimate for the gradient of a function multiplied by the designated scaled cutoff.
--
--   Let $E$ be a finite-dimensional complete real inner product space. Denote the fixed bump `Energy.Euclidean.LipschitzApproximation.bump` by $\beta$, and its scaled cutoff `Energy.Euclidean.LipschitzApproximation.scaled R` by $\chi_R$. Assume:
--
--   1. $R,M\in\mathbb R$ and $R>0$.
--   2. $\|D\beta(y)\|\le M$ for every $y\in E$, where the norm is the operator norm of the Fréchet derivative.
--   3. $f:E\to\mathbb R$ is differentiable at $x\in E$.
--
--   Then
--   $$
--   \|\nabla(\chi_R f)(x)\|^2
--   \le 2\|\nabla f(x)\|^2+2(M/R)^2 f(x)^2.
--   $$
--   This technical estimate controls the energy contribution introduced by cutoff multiplication. It requires no measure or global differentiability assumption on $f$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_gradient_scaled_mul_sq_le {R M : ℝ} (hR : 0 < R)
--       (hM : ∀ x : E, ‖fderiv ℝ (⇑(Energy.Euclidean.LipschitzApproximation.bump (E := E))) x‖ ≤ M)
--       {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
--       ‖gradient (fun y => Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 ≤
--         2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/WeakLimit`](https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9).
--
--   Definition modules: [`Analysis/Cutoff/SmoothBall`](https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63).
--
--   Previous: [`tendsto_integral_scaled_mul`](https://prove2.me/theorems/068f0f8e-b98a-4f43-90a9-f224447633d6) · Next: [`tendsto_energy_scaled_mul`](https://prove2.me/theorems/7ebf926b-52bf-46f9-b74c-32dbc8febfcb).
--
--   [Source excerpt, lines 343–347](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L343-L347) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L341-L419 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable [FiniteDimensional ℝ E]
omit [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le_readable {R M : ℝ} (hR : 0 < R)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(Energy.Euclidean.LipschitzApproximation.bump (E := E))) x‖ ≤ M)
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    ‖gradient (fun y => Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 ≤
      2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by sorry
