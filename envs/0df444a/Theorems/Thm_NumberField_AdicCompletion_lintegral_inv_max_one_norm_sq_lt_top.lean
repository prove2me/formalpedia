-- Prove2me | Theorems.Thm_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top
-- name    : NumberField.AdicCompletion.lintegral_inv_max_one_norm_sq_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3132b768-3ec7-5ae2-aeaf-38d22a8e0a81
-- title:
--   Finiteness of int max(1,‖y‖)⁻² dν on L_w
-- statement:
--   Let $L$ be a number field and let $w$ be a point of the height-one spectrum of its ring of integers $\mathcal{O}_L$, that is, a nonzero prime ideal of $\mathcal{O}_L$; write $L_w$ for the $w$-adic completion of $L$, equipped with its canonical norm $\|\cdot\|$ coming from the $w$-adic valuation, together with a measurable space structure on $L_w$ that is assumed to be the Borel structure of its topology. Let $\nu$ be a measure on $L_w$ which is an additive Haar measure, i.e. a translation-invariant regular measure, finite on compacta and positive on nonempty open sets. The assertion is that the lower Lebesgue integral, with values in $[0,\infty]$, of the function $y \mapsto \bigl(\max(1,\|y\|)^2\bigr)^{-1}$ against $\nu$ is strictly less than $\infty$; here the real number $\max(1,\|y\|)^2$ is first pushed into $[0,\infty]$ via `ENNReal.ofReal` and then inverted in $[0,\infty]$, so the integrand is $\min(1,\|y\|^{-2})$ in the extended-nonnegative-real sense. No normalisation of $\nu$ is imposed, and no value of the integral is asserted, only its finiteness.
--
--   This is the elementary local integrability statement that the inverse square of $\max(1,\|y\|)$ is $\nu$-integrable on a nonarchimedean completion of a number field, in the shape of a finiteness assertion for a lower Lebesgue integral. It is used in the lower-unipotent absorption step recorded in [`AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet`](thm.html#AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.AdicCompletion.lintegral_inv_max_one_norm_sq_lt_top
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    [MeasurableSpace (w.adicCompletion L)] [BorelSpace (w.adicCompletion L)]
    (ν : Measure (w.adicCompletion L)) [ν.IsAddHaarMeasure] :
    ∫⁻ y : w.adicCompletion L, (ENNReal.ofReal ((max 1 ‖y‖) ^ 2))⁻¹ ∂ν < ⊤ := by sorry
