-- Prove2me | Theorems.Thm_MeasureTheory_setLIntegral_comp_smul
-- name    : MeasureTheory.setLIntegral_comp_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:03:45.426271+00:00
-- url     : https://prove2.me/theorems/7c07de50-3504-4205-824c-0d310025a847
-- title:
--   Change of variables for a dilation in a set-restricted lower Lebesgue integral
-- statement:
--   Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$, let $g:E\to[0,\infty]$ be arbitrary, let $S\subseteq E$ be arbitrary and let $r\neq0$ be a real number. Then
--   $$\int_{S}^{*} g(r\,w)\,d\mu(w)\;=\;\bigl|r^{\,\dim E}\bigr|^{-1}\int_{rS}^{*} g(y)\,d\mu(y),$$
--   where the integrals are lower Lebesgue integrals and $rS=\{r\,s: s\in S\}$.
--
--   **Role.** This is the change of variables for a dilation, in the form needed when neither the set nor the integrand can be assumed measurable. Mathlib records how a Haar measure transforms under a dilation, $\mu(rS)=|r^{\dim E}|\,\mu(S)$, and it has the change of variables for the Bochner integral of a scaled function; the corresponding statement for a set-restricted lower Lebesgue integral, which is what one needs for quantities defined as lower integrals of a priori non-measurable expressions, is not available. The Korevaar–Schoen energy of a map from a planar domain into a metric space is exactly such a quantity: it is a lower integral of the difference quotient $d(u(w),u(z))^2$, and a map into a general metric space is not assumed measurable. The identity above is what converts a rescaling of the plane into an explicit power of $r$, and hence what makes the energy of a homogeneous map an exact power of the radius.
--
--   **The argument.** Multiplication by $r$ is a homeomorphism of $E$, hence a measurable equivalence $R$, and $R^{-1}(rS)=S$ because $r\neq0$. Restricting a measure along a measurable equivalence commutes with pushing it forward, so the pushforward of $\mu|_S$ under $R$ is the restriction to $rS$ of the pushforward of $\mu$. Since a measurable equivalence is a measurable embedding, the lower integral against a pushforward measure equals the lower integral of the composite — with no measurability hypothesis on the integrand. Finally the pushforward of a Haar measure under a dilation is $|r^{\dim E}|^{-1}\mu$, and a scalar multiple of the measure pulls out of the integral.
-- source:
--   The Haar scaling law Measure.map_addHaar_smul and MeasureTheory.Measure.addHaar_smul of Mathlib (Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar), combined with MeasureTheory.lintegral_map_equiv and MeasurableEquiv.restrict_map; the Bochner counterpart is MeasureTheory.integral_comp_smul in Mathlib.MeasureTheory.Measure.Haar.NormedSpace.

import Mathlib

namespace MeasureTheory

open scoped Pointwise

universe u

theorem setLIntegral_comp_smul {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : E → ENNReal) (S : Set E) (r : ℝ) (hr : r ≠ 0) :
    ∫⁻ w in S, g (r • w) ∂mu
      = ENNReal.ofReal |r ^ Module.finrank ℝ E|⁻¹ * ∫⁻ y in r • S, g y ∂mu := by sorry

end MeasureTheory
