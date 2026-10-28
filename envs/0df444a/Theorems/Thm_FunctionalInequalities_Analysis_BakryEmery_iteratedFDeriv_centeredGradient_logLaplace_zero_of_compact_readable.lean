-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:11.064888+00:00
-- url     : https://prove2.me/theorems/c850afc5-a923-4019-b001-39ff0f56dd9b
-- title:
--   Cumulant Vectors from Centered Log-Laplace Derivatives
-- statement:
--   This is a finite-dimensional identity for the derivatives of a centered log-Laplace gradient.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$ whose support is compact. For every integer $r\ge 1$ and every map $h:\operatorname{Fin}(r)\to E$, define $\Lambda=\log\operatorname{Laplace}(\mu)$. Then the $r$-th iterated derivative at $0$ of the map $z\mapsto\nabla\Lambda(z)-\nabla\Lambda(0)$, applied to $h$, equals the cumulant Riesz vector associated with the list of directions represented by $h$.
--
--   $$D^r\bigl(\nabla\Lambda-\nabla\Lambda(0)\bigr)(0)[h]=\operatorname{cumulantVector}(\mu,\operatorname{List.ofFn}(h)).$$
--
--   Here `iteratedFDeriv` is the iterated Fréchet derivative and `cumulantVector` is the Riesz vector associated with the corresponding cumulant functional. The result is a technical bridge between derivatives of the log-Laplace transform and cumulant tensors.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (r : ℕ) (hr : 1 ≤ r) (h : Fin r → E) :
--       iteratedFDeriv ℝ r (fun z : E =>
--         gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) 0 h =
--         cumulantVector (μ : Measure E) (List.ofFn h)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`inner_iteratedFDeriv_gradient_apply`](https://prove2.me/theorems/98bdd014-ddd3-4c09-a9f1-90cc5a041bc5), [`iteratedFDeriv_sub_const_of_pos`](https://prove2.me/theorems/5eae9d29-35ba-4434-ad2d-a584e6ef24b4).
--
--   Previous: [`cumulant_two_eq_centered_moment_of_integrable_exp`](https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb) · Next: [`inner_cumulantVector_single_ringInverse_cumulantVector`](https://prove2.me/theorems/9237a40c-7f1f-4233-8865-0d20c1925f94).
--
--   [Source excerpt, lines 608–612](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L608-L612) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L606-L651 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (r : ℕ) (hr : 1 ≤ r) (h : Fin r → E) :
    iteratedFDeriv ℝ r (fun z : E =>
      gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) 0 h =
      cumulantVector (μ : Measure E) (List.ofFn h) := by sorry
