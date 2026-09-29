-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
-- name    : MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/8edb730f-d58e-5042-8061-6413605f140e
-- title:
--   Dirichlet localisation: int h(t)sin(Rt)/t → π h(0)
-- statement:
--   Let $h\colon\mathbb{R}\to\mathbb{C}$ be Lebesgue integrable on $\mathbb{R}$ (with respect to the volume measure), suppose that its Fourier transform $\mathcal{F}h$, normalised as in Mathlib by $(\mathcal{F}h)(u)=\int_{\mathbb{R}} e^{-2\pi i t u} h(t)\,dt$, is also integrable, and suppose that $h$ is continuous at the point $0$. Then, as $R\to+\infty$ along the filter `atTop` on $\mathbb{R}$, the integrals
--   $$\int_{\mathbb{R}} \frac{\sin(Rt)}{t}\,h(t)\,dt$$
--   converge to $\pi\,h(0)$ in $\mathbb{C}$. Here the factor $\sin(Rt)/t$ is formed in $\mathbb{R}$ and then coerced to $\mathbb{C}$, so that at $t=0$ it is $0$ by the junk-value convention for division; this affects the integrand only on a null set. No integrability of the individual integrands is hypothesised: the assertion is convergence of the Bochner integrals of the functions $t\mapsto (\sin(Rt)/t)\,h(t)$, an integral being $0$ by convention should some integrand fail to be integrable.
--
--   This is Dirichlet's localisation lemma (Fourier's single-integral formula at a point of continuity), the statement that the Dirichlet kernel $\sin(Rt)/(\pi t)$ acts as an approximate identity against a function whose Fourier transform is integrable. It is used in the analytic estimates behind [`AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz), where oscillatory integrals against such kernels are localised at a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped FourierTransform

theorem MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
    (h : ℝ → ℂ) (hh : MeasureTheory.Integrable h)
    (hFh : MeasureTheory.Integrable (𝓕 h)) (h0 : ContinuousAt h 0) :
    Filter.Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t)
      Filter.atTop (nhds ((Real.pi : ℂ) * h 0)) := by sorry
