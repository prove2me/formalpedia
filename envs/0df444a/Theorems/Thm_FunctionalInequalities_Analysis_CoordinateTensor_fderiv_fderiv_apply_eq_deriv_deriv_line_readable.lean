-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_fderiv_fderiv_apply_eq_deriv_deriv_line_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_apply_eq_deriv_deriv_line_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:55.239057+00:00
-- url     : https://prove2.me/theorems/91499aa3-4a30-4b4f-af4c-05085add7997
-- title:
--   Second Fréchet Derivative Along a Line
-- statement:
--   This statement identifies a second Fréchet derivative evaluated twice in one direction with a one-dimensional second derivative.
--
--   Let $W$ be a real normed space, let $\Phi:W\to\mathbb R$, and let $y\in W$. Assume $\Phi$ is $C^2$ at $y$. For every $v\in W$,
--
--   $$
--   \bigl(D(D\Phi)(y)v\bigr)v
--   =\left.\frac{d^2}{d\varepsilon^2}\Phi(y+\varepsilon v)\right|_{\varepsilon=0}.
--   $$
--
--   This general calculus identity is used to convert second directional derivatives into derivatives along scalar lines.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_fderiv_apply_eq_deriv_deriv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
--       {Φ : W → ℝ} {y : W} (hΦ : ContDiffAt ℝ 2 Φ y) (v : W) :
--       fderiv ℝ (fderiv ℝ Φ) y v v = deriv (deriv fun ε : ℝ => Φ (y + ε • v)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Previous: [`sum_mul_prod_delta_erase_erase`](https://prove2.me/theorems/76502fa4-2d8b-4cb4-b4ba-234b9fc000dc) · Next: [`slot_sum_two`](https://prove2.me/theorems/e0d1f1e6-4957-4586-aef5-50f1a34f8224).
--
--   [Source excerpt, lines 613–615](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L613-L615) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L611-L644 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_apply_eq_deriv_deriv_line`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_apply_eq_deriv_deriv_line_readable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : W → ℝ} {y : W} (hΦ : ContDiffAt ℝ 2 Φ y) (v : W) :
    fderiv ℝ (fderiv ℝ Φ) y v v = deriv (deriv fun ε : ℝ => Φ (y + ε • v)) 0 := by sorry
