-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:34.736634+00:00
-- url     : https://prove2.me/theorems/2ebfc9d7-c5cf-4a67-b311-d32be10eee98
-- title:
--   Third Cumulant Contraction Bound
-- statement:
--   This is the local-moment form of Lemma 4.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be a probability measure on a finite-dimensional real inner-product space $E$. Assume:
--
--   1. $r>0$ and $e^{r\|x\|}$ is integrable with respect to $\mu$.
--   2. $\mu$ is centered: $\int\langle v,x\rangle\,d\mu(x)=0$ for every $v\in E$.
--   3. $\mu$ is isotropic: $\int\langle v,x\rangle\langle w,x\rangle\,d\mu(x)=\langle v,w\rangle$.
--   4. $\mu$ satisfies `LetwinQuadraticBound`.
--
--   Then for every $u\in E$, with $e_j$ the standard orthonormal basis,
--
--   $$\sum_{j,k}\kappa_3(u,e_j,e_k)^2\le 8\|u\|^2.$$
--
--   This is the Hilbert–Schmidt contraction estimate for the third cumulant under the stated local exponential-moment assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_sq_cumulant_three_le_of_letwin_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
--       (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) (u : E) :
--       ∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
--         8 * ‖u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`cumulant_three_eq_integral_of_integrable_exp`](https://prove2.me/theorems/2207a4d5-d176-43bd-8980-82729562a6ee), [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818).
--
--   Previous: [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818) · Next: [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis`](https://prove2.me/theorems/d843d70e-8af8-4774-b08a-b195f310d902).
--
--   [Source excerpt, lines 232–236](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L232-L236) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L229-L333 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_readable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by sorry
