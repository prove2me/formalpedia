-- Prove2me | Theorems.Thm_NumberField_AdicCompletion_lintegral_comp_torusAffineChart_mul_eq_lintegral
-- name    : NumberField.AdicCompletion.lintegral_comp_torusAffineChart_mul_eq_lintegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0e25420d-0716-5e7b-93d9-16c0c0eded14
-- title:
--   Jacobian identity for the torus chart on GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field and $v$ a height-one prime of its ring of integers $\mathcal{O}_K$, and let $F = K_v$ be the associated adic completion, equipped with a measurable space structure assumed to be its Borel structure; let $\mu$ be an additive Haar measure on $F$, and let $\mu^{\otimes 4}$ denote the product measure on $F^4 = (\mathrm{Fin}\ 4 \to F)$. Let $d \in F$ be an element that is not a square, and let $H \colon F^4 \to [0,\infty]$ be a measurable function with values in the extended non-negative reals. Writing a point of $F^4$ as $q = (q_0,q_1,q_2,q_3)$, the assertion is the equality of lower Lebesgue integrals
--   $$\int_{F^4} H\bigl(q_3 + q_2 q_0,\; q_2 q_1,\; d q_2 + q_3 q_0,\; q_3 q_1\bigr)\cdot \|q_1\|\,\|q_3^2 - d q_2^2\| \; d\mu^{\otimes 4}(q) \;=\; \int_{F^4} H(x)\, d\mu^{\otimes 4}(x),$$
--   where $\|\cdot\|$ is the absolute value of $F$ and the real weight $\|q_1\|\,\|q_3^2 - d q_2^2\|$ enters through its image in $[0,\infty]$. No normalisation of $\mu$ is imposed: both sides scale in the same way under scaling of $\mu$.
--
--   This is the change-of-variables (Jacobian) identity for the factorisation of a matrix $g \in \mathrm{GL}_2(F)$ as a product $t\,\sigma$, with $t$ in the non-split torus attached to $F[\sqrt{d}]$ and $\sigma$ lower triangular with top-left entry $1$: in the coordinates $q = (a,b,r,p)$ the product map transports $\|b\|\,\|p^2 - d r^2\|\,d\mu^{\otimes 4}$ to the additive Haar measure of the space of $2 \times 2$ matrices, the factor $\|p^2-dr^2\|$ being the modulus of the torus element. It feeds the computation of orbital integrals over a non-split torus in the local harmonic analysis used for the Langlands–Tunnell theorem, and is cited by [`AutomorphicForm.eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare`](thm.html#AutomorphicForm.eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdicCompletion_lintegral_comp_torusAffineChart_mul_eq_lintegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem NumberField.AdicCompletion.lintegral_comp_torusAffineChart_mul_eq_lintegral
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (d : v.adicCompletion K) (hd : ¬ IsSquare d)
    (H : (Fin 4 → v.adicCompletion K) → ENNReal) (hH : Measurable H) :
    ∫⁻ q, H ![q 3 + q 2 * q 0, q 2 * q 1, d * q 2 + q 3 * q 0, q 3 * q 1] *
        ENNReal.ofReal (‖q 1‖ * ‖q 3 ^ 2 - d * q 2 ^ 2‖) ∂(Measure.pi fun _ : Fin 4 => μ) =
      ∫⁻ x, H x ∂(Measure.pi fun _ : Fin 4 => μ) := by sorry
