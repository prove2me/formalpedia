-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_tendsto_energy_scaled_mul_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:37.31099+00:00
-- url     : https://prove2.me/theorems/7ebf926b-52bf-46f9-b74c-32dbc8febfcb
-- title:
--   Energy Convergence of Scaled Cutoff Products
-- statement:
--   This statement gives convergence of smooth-test energies under the designated expanding cutoffs.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure and $\mu$ a finite measure. Let $f:E\to\mathbb R$ be admissible (`Poincare.SmoothTest.Admissible`): $f$ is $C^\infty$, belongs to $L^2(\mu)$, and $\|\nabla f\|^2$ is integrable. For $R>0$, let $\chi_R$ denote `Energy.Euclidean.LipschitzApproximation.scaled R`. Define the energy (`Poincare.SmoothTest.energy`) by $\mathcal E_\mu(g)=\int\|\nabla g\|^2\,d\mu$.
--
--   As $n\in\mathbb N$ tends to infinity,
--   $$
--   \mathcal E_\mu(\chi_{n+1}f)\longrightarrow\mathcal E_\mu(f).
--   $$
--   This is an energy approximation statement for extending inequalities from compactly supported smooth tests to admissible tests. The energy has no factor of $1/2$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_energy_scaled_mul {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
--       (hf : Admissible μ f) :
--       Tendsto (fun n : ℕ =>
--           energy μ (fun x => Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x))
--         atTop (𝓝 (energy μ f))
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/WeakLimit`](https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9).
--
--   Definition modules: [`Analysis/Cutoff/SmoothBall`](https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63), [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Supporting theorems: [`norm_gradient_scaled_mul_sq_le`](https://prove2.me/theorems/1194b2a8-bd6e-4efd-bc86-f6b48715f7e0).
--
--   Previous: [`norm_gradient_scaled_mul_sq_le`](https://prove2.me/theorems/1194b2a8-bd6e-4efd-bc86-f6b48715f7e0) · Next: [`Holds.of_compactSupport`](https://prove2.me/theorems/7a878356-8017-4c9f-ae31-615b3aebf1ac).
--
--   [Source excerpt, lines 422–426](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L422-L426) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L421-L528 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

open MeasureTheory ProbabilityTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul_readable {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : Admissible μ f) :
    Tendsto (fun n : ℕ =>
        energy μ (fun x => Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x))
      atTop (𝓝 (energy μ f)) := by sorry
