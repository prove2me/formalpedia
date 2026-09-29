-- Prove2me | Theorems.Thm_NumberField_AdicCompletion_lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
-- name    : NumberField.AdicCompletion.lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8ac7f00f-2bca-5a60-81c4-39e71d8640fe
-- title:
--   Jacobian of the torus–unipotent product chart over L⊗_K Kᵥ
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $E = L \otimes_K K_v$ be the base change of $L$ to the completion $K_v$ of $K$ at $v$, equipped with a measurable space structure that is the Borel $\sigma$-algebra of its topology. Let $\nu$ be an additive Haar measure on $E$, and let $\nu^{4}$ denote the product measure $\bigotimes_{i\in\mathrm{Fin}\,4}\nu$ on $E^{4}$, identified with functions $\mathrm{Fin}\,4 \to E$. Then for every measurable $H \colon E^{4} \to [0,\infty]$,
--   $$\int_{E^{4}} H\bigl(q_0 + q_0q_1q_2,\ q_0q_1,\ q_3q_2,\ q_3\bigr)\,\bigl\|N_{E/K_v}(q_0q_3)\bigr\|\,\mathrm{d}\nu^{4}(q) = \int_{E^{4}} H(x)\,\mathrm{d}\nu^{4}(x),$$
--   where $N_{E/K_v}$ is the algebra norm of $E$ over $K_v$ and the real number $\|N_{E/K_v}(q_0q_3)\|$ enters as its image in $[0,\infty]$ under `ENNReal.ofReal`. Both sides are lower Lebesgue integrals of $[0,\infty]$-valued functions, so no integrability hypothesis is needed.
--
--   This is the change-of-variables identity for the product chart on $\mathrm{GL}_2(E)$ sending $(t_1,x,y,t_2)$ to $\mathrm{diag}(t_1,t_2)\begin{pmatrix}1+xy & x\\ y & 1\end{pmatrix}$, written out in the four matrix coordinates: the chart transports $\|N_{E/K_v}(t_1t_2)\|\,\mathrm{d}\nu^{4}$ to $\nu^{4}$, the factor being the Jacobian of the map in these coordinates. It is used in the semi-local orbital integral computations, where [`AutomorphicForm.lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart`](thm.html#AutomorphicForm.lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart) decomposes an integral against semi-local Haar measure into an integral over the diagonal torus and the unipotent coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdicCompletion_lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.AdicCompletion.lintegral_tensor_comp_splitTorusProductChart_mul_norm_algebraNorm_eq_lintegral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (H : (Fin 4 → L ⊗[K] v.adicCompletion K) → ENNReal) (hH : Measurable H) :
    ∫⁻ q, H ![q 0 + q 0 * q 1 * q 2, q 0 * q 1, q 3 * q 2, q 3] *
        ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (q 0 * q 3)‖
          ∂(Measure.pi fun _ : Fin 4 => ν) =
      ∫⁻ x, H x ∂(Measure.pi fun _ : Fin 4 => ν) := by sorry
