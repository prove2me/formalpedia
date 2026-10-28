-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:20.740993+00:00
-- url     : https://prove2.me/theorems/d843d70e-8af8-4774-b08a-b195f310d902
-- title:
--   Third Cumulant Bound in Any Orthonormal Basis
-- statement:
--   This formalizes the basis-independent form of Lemma 4.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 18.
--
--   Let $\mu$ be a probability measure on a finite-dimensional real inner-product space $E$. Assume $r>0$, $e^{r\|x\|}$ is integrable, $\mu$ is centered and isotropic, and $\mu$ satisfies `LetwinQuadraticBound`. For any orthonormal basis $b$ indexed by $\operatorname{Fin}(m)$ and any $u\in E$,
--
--   $$\sum_{j,k}\kappa_3(u,b_j,b_k)^2\le 8\|u\|^2.$$
--
--   The result transports the third-cumulant Hilbert–Schmidt estimate from the standard orthonormal basis to every orthonormal basis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis (μ : Measure E) [IsProbabilityMeasure μ]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
--       (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
--       (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫)
--       (hL : LetwinQuadraticBound μ) {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
--       ∑ j, ∑ k, cumulant μ 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp`](https://prove2.me/theorems/2ebfc9d7-c5cf-4a67-b311-d32be10eee98), [`sum_coordTensor_sq_eq`](https://prove2.me/theorems/43928816-0a65-4412-bbe2-8abe0018771e).
--
--   Previous: [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp`](https://prove2.me/theorems/2ebfc9d7-c5cf-4a67-b311-d32be10eee98) · Next: [`cumulant_two_eq_centered_moment_of_integrable_exp`](https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb).
--
--   [Source excerpt, lines 359–364](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L359-L364) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.2, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L358-L380 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_readable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫)
    (hL : LetwinQuadraticBound μ) {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by sorry
