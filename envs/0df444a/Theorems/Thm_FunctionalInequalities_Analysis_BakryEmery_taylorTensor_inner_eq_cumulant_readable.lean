-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_inner_eq_cumulant_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:19.774983+00:00
-- url     : https://prove2.me/theorems/777bcca0-0906-41de-8616-b3ae233c3880
-- title:
--   Taylor Tensor of a Linear Observable
-- statement:
--   This formalizes the linear-function identity from Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be a finite nonzero measure on a finite-dimensional real inner-product space $E$, assume that $e^{r\|x\|}$ is integrable for every $r\in\mathbb R$, and let $v\in E$, $d\in\mathbb N$, and $h:\operatorname{Fin}(d)\to E$. Then
--
--   $$T_d\bigl(x\mapsto\langle v,x\rangle\bigr)(h)
--   =\frac{1}{d!}\,\kappa_{d+1}(v,h_0,\ldots,h_{d-1}),$$
--
--   where `taylorTensor` is $T_d$ and `cumulant` is the $(d+1)$-st derivative tensor of the logarithmic Laplace transform at the origin.
--
--   This connects Taylor tensors of linear observables with cumulant tensors and is used in tensor-norm estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_inner_eq_cumulant (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
--       (h : Fin d → E) :
--       taylorTensor μ (fun x => ⟪v, x⟫) d h = (d.factorial : ℝ)⁻¹ * cumulant μ (d + 1) (Fin.cons v h)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`tiltAverage_inner_eq_fderiv_logLaplace`](https://prove2.me/theorems/6e9a8c5a-1811-461e-b918-2514d0abe6ef).
--
--   Previous: [`tiltAverage_inner_eq_fderiv_logLaplace_of_lt`](https://prove2.me/theorems/e5acfca7-aa88-4d8d-9c36-ad0061799915) · Next: [`norm_coordTensor_taylorTensor_inner_sq_le_of_basis`](https://prove2.me/theorems/f6507f16-38d4-4c99-9d45-dccf8890a2d6).
--
--   [Source excerpt, lines 332–335](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L332-L335) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L330-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_readable (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
    (h : Fin d → E) :
    taylorTensor μ (fun x => ⟪v, x⟫) d h = (d.factorial : ℝ)⁻¹ * cumulant μ (d + 1) (Fin.cons v h) := by sorry
