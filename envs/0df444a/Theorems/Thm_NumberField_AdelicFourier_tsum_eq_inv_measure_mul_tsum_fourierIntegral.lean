-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral
-- name    : NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/51852f28-eb73-577c-9deb-14daa676ba9d
-- title:
--   Adelic Poisson summation on the Schwartz–Bruhat space
-- statement:
--   Let $F$ be a number field, and equip its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` with a measurable space structure that is the Borel structure of its topology, and with a measure $\mu$ that is an additive Haar measure. Let $\psi : \mathbb{A}_F \to \mathbb{C}$ be an additive character satisfying `IsGlobalAddChar F ψ`, i.e. $\psi(\iota\alpha) = 1$ for every $\alpha \in F$, where $\iota =$ `algebraMap F (AdeleRing (𝓞 F) F)` is the diagonal embedding, $\psi$ is continuous, and $\psi$ is not the trivial character. Let $f : \mathbb{A}_F \to \mathbb{C}$ lie in the Schwartz–Bruhat space `schwartzBruhat F`, the $\mathbb{C}$-linear span of the functions $x \mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the mixed space of $F$ (the infinite component being transported along `InfiniteAdeleRing.ringEquiv_mixedSpace F`) and $h$ a locally constant, compactly supported function on the finite adele ring. Then
--   $$\sum_{\xi \in F} f(\iota\xi) \;=\; \mu(B)^{-1}\sum_{\xi \in F} \mathcal{F}_{\psi,\mu}f(\iota\xi),$$
--   where $\mathcal{F}_{\psi,\mu}f(w) = \int_{\mathbb{A}_F} \psi(-(vw))f(v)\,\mathrm{d}\mu(v)$ and $B =$ `AdelicBox.adelicBox F` is the set of adeles whose infinite part lies in the preimage of the fundamental domain of the lattice basis of $\mathcal{O}_F$ in the mixed space and whose finite part is integral at every finite place; the scalar $\mu(B)^{-1}$ is the inverse of the real number $\mu(B)$ viewed in $\mathbb{C}$. No normalisation of $\mu$ is imposed, the factor $\mu(B)^{-1}$ being carried explicitly.
--
--   This is the adelic Poisson summation formula for a global additive character and a Schwartz–Bruhat test function, in the form with the volume of the adelic box appearing as an explicit normalising factor. It is used in the computation of Whittaker coefficients and in the spectral side of the adelic trace formula for $\mathrm{GL}_2$, being cited by [`AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact`](thm.html#AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact) and by [`NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero`](thm.html#NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
