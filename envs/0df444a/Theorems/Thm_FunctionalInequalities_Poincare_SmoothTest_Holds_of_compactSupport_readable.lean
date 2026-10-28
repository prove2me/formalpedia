-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_Holds_of_compactSupport_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:48.394983+00:00
-- url     : https://prove2.me/theorems/7a878356-8017-4c9f-ae31-615b3aebf1ac
-- title:
--   Extension of Compactly Supported Smooth-Test Poincaré Bounds
-- statement:
--   This is the compact-support extension step associated with the regular-approximation reduction in Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered).
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure, let $\mu$ be a probability measure, and let $C\in\mathbb R$. Assume:
--
--   1. $C\ge0$.
--   2. Every compactly supported admissible $f:E\to\mathbb R$ satisfies $\operatorname{Var}_\mu(f)\le C\mathcal E_\mu(f)$.
--
--   Here admissibility (`Poincare.SmoothTest.Admissible`) means $C^\infty$ smoothness, membership in $L^2(\mu)$, and integrability of $\|\nabla f\|^2$; $\mathcal E_\mu(f)=\int\|\nabla f\|^2\,d\mu$ is `Poincare.SmoothTest.energy`.
--
--   Then `Poincare.SmoothTest.Holds μ C` holds, namely
--   $$
--   \operatorname{Var}_\mu(f)\le C\int\|\nabla f\|^2\,d\mu
--   \quad\text{for every admissible }f.
--   $$
--   This removes the compact-support restriction on the tests. It does not assume log-concavity or establish the paper's regular-density conditions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Holds.of_compactSupport {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ} (hC : 0 ≤ C)
--       (h : ∀ f : E → ℝ, Admissible μ f → HasCompactSupport f → variance f μ ≤ C * energy μ f) :
--       Holds μ C
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/WeakLimit`](https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9).
--
--   Definition modules: [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Supporting theorems: [`Admissible.of_contDiff_hasCompactSupport`](https://prove2.me/theorems/7f79ab39-6c03-4d68-870d-2dd02d1e1b0b), [`tendsto_energy_scaled_mul`](https://prove2.me/theorems/7ebf926b-52bf-46f9-b74c-32dbc8febfcb), [`tendsto_integral_scaled_mul`](https://prove2.me/theorems/068f0f8e-b98a-4f43-90a9-f224447633d6).
--
--   Previous: [`tendsto_energy_scaled_mul`](https://prove2.me/theorems/7ebf926b-52bf-46f9-b74c-32dbc8febfcb).
--
--   [Source excerpt, lines 532–534](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L532-L534) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L530-L594 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

open MeasureTheory ProbabilityTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_readable {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : E → ℝ, Admissible μ f → HasCompactSupport f → variance f μ ≤ C * energy μ f) :
    Holds μ C := by sorry
