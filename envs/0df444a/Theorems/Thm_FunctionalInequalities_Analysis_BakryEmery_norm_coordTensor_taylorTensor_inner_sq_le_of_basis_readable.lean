-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_coordTensor_taylorTensor_inner_sq_le_of_basis_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:24.273223+00:00
-- url     : https://prove2.me/theorems/f6507f16-38d4-4c99-9d45-dccf8890a2d6
-- title:
--   Coordinate Tensor Bound in an Arbitrary Orthonormal Basis
-- statement:
--   This formalizes the linear-function step cited on page 30 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Proposition 7.1.
--
--   Let $\mu$ be a probability measure on a finite-dimensional real inner-product space $E$ with all exponential moments. Let $b_E$ be an orthonormal basis indexed by $\operatorname{Fin}(m)$. Fix $d\in\mathbb N$, $b\in\mathbb R$, and assume that for every $u\in E$,
--
--   $$\sum_{J:\operatorname{Fin}(d)\to\operatorname{Fin}(m)}\kappa_{d+1}(u,b_E\circ J)^2\le b\|u\|^2.$$
--
--   Then for every $v\in E$,
--
--   $$\left\|\operatorname{coordTensor}_{b_E}\!\left(T_d(x\mapsto\langle v,x\rangle)\right)\right\|^2
--   \le \frac{b}{(d!)^2}\|v\|^2.$$
--
--   The result transfers a cumulant contraction estimate to the coordinate tensor of the Taylor tensor in any orthonormal basis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_coordTensor_taylorTensor_inner_sq_le_of_basis (μ : Measure E) [IsProbabilityMeasure μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {m : ℕ}
--       (bE : OrthonormalBasis (Fin m) ℝ E) {d : ℕ} {b : ℝ}
--       (hR : ∀ u : E, ∑ J : Fin d → Fin m,
--         cumulant μ (d + 1) (Fin.cons u fun k => bE (J k)) ^ 2 ≤ b * ‖u‖ ^ 2) (v : E) :
--       ‖Analysis.Tensor.coordTensor bE (taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
--         b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`taylorTensor_inner_eq_cumulant`](https://prove2.me/theorems/777bcca0-0906-41de-8616-b3ae233c3880).
--
--   Previous: [`taylorTensor_inner_eq_cumulant`](https://prove2.me/theorems/777bcca0-0906-41de-8616-b3ae233c3880) · Next: [`contDiffOn_logLaplace_ball`](https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef).
--
--   [Source excerpt, lines 721–727](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L721-L727) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L718-L755 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {m : ℕ}
    (bE : OrthonormalBasis (Fin m) ℝ E) {d : ℕ} {b : ℝ}
    (hR : ∀ u : E, ∑ J : Fin d → Fin m,
      cumulant μ (d + 1) (Fin.cons u fun k => bE (J k)) ^ 2 ≤ b * ‖u‖ ^ 2) (v : E) :
    ‖Analysis.Tensor.coordTensor bE (taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by sorry
