-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_exists_norm_taylorTensor_le_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:04.372999+00:00
-- url     : https://prove2.me/theorems/3b9f7ced-1180-435b-b7cb-81230ca3ce07
-- title:
--   Continuity Bound for Taylor Tensors
-- statement:
--   This formalizes the operator-norm continuity estimate for Taylor tensors associated with a probability measure having all exponential moments.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a probability measure on $E$, and assume that for every $r\in\mathbb R$ the function $x\mapsto e^{r\|x\|}$ is integrable with respect to $\mu$. Then, for every $d\in\mathbb N$, there exists a real constant $C$ such that every $f:E\to\mathbb R$ with $f\in L^2(\mu)$ satisfies
--
--   $$\|T_d f\|\le C\,\bigl(\|f\|_{L^2(\mu)}\bigr),$$
--
--   where `taylorTensor μ f d` is the Taylor tensor and the Lean expression for the $L^2$ norm is `(eLpNorm f 2 μ).toReal`.
--
--   This gives a boundedness statement for the map $f\mapsto T_d f$ at each fixed order $d$. The constant may depend on $\mu$ and $d$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_norm_taylorTensor_le (μ : Measure E) [IsProbabilityMeasure μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
--       ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ → ‖taylorTensor μ f d‖ ≤ C * (eLpNorm f 2 μ).toReal
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82), [`iteratedFDeriv_integral_exp_inner_smul`](https://prove2.me/theorems/5c6a3c00-e76c-4094-bd9b-db3f77cc3227).
--
--   Previous: [`taylorTensor_const_mul`](https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959) · Next: [`exists_norm_coordTensor_taylorTensor_le`](https://prove2.me/theorems/f14f3dc2-aea1-4b21-93e6-8c5ccce91407).
--
--   [Source excerpt, lines 500–502](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L500-L502) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L498-L555 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ → ‖taylorTensor μ f d‖ ≤ C * (eLpNorm f 2 μ).toReal := by sorry
