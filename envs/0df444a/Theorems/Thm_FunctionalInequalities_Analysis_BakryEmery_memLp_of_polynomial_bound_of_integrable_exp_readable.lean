-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_memLp_of_polynomial_bound_of_integrable_exp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.memLp_of_polynomial_bound_of_integrable_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:15.428811+00:00
-- url     : https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818
-- title:
--   Polynomial Growth Implies Square Integrability
-- statement:
--   This theorem gives an $L^2$ consequence of one positive exponential moment.
--
--   Let $\mu$ be a probability measure on a measurable normed space $E$. Suppose that some $r>0$ satisfies $x\mapsto e^{r\|x\|}\in L^1(\mu)$. Let $g:E\to\mathbb R$ be continuous and assume that, for some $C\in\mathbb R$ and $k\in\mathbb N$,
--
--   $$\|g(x)\|\le C(1+\|x\|)^k\qquad\text{for every }x\in E.$$
--
--   Then $g\in L^2(\mu)$, expressed in Lean as `MemLp g 2 μ`. This is a technical integrability criterion used for polynomially bounded observables.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_of_polynomial_bound_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
--       {g : E → ℝ} (hg : Continuous g) {C : ℝ} {k : ℕ}
--       (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) : MemLp g 2 μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Previous: [`cumulant_three_eq_integral_of_integrable_exp`](https://prove2.me/theorems/2207a4d5-d176-43bd-8980-82729562a6ee) · Next: [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp`](https://prove2.me/theorems/2ebfc9d7-c5cf-4a67-b311-d32be10eee98).
--
--   [Source excerpt, lines 186–189](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L186-L189) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L184-L202 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.memLp_of_polynomial_bound_of_integrable_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.memLp_of_polynomial_bound_of_integrable_exp_readable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → ℝ} (hg : Continuous g) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) : MemLp g 2 μ := by sorry
