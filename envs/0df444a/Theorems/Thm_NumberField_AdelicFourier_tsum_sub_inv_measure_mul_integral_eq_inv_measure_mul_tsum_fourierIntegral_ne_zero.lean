-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
-- name    : NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/67f37134-4f52-5eca-a84c-ed356a96f47b
-- title:
--   Adelic Poisson summation with the zero frequency split off
-- statement:
--   Let $F$ be a number field, equipped with a measurable space structure on its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` which is the Borel structure of the topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi : \mathbb{A}_F \to \mathbb{C}$ be an additive character satisfying the project's predicate `IsGlobalAddChar`, i.e. $\psi$ is continuous, is not the trivial character, and satisfies $\psi(\alpha) = 1$ for every $\alpha$ in the image of $F$ under the structure map $F \to \mathbb{A}_F$. Let $f$ lie in `schwartzBruhat F`, the $\mathbb{C}$-span of the pure tensors $x \mapsto g(x_\infty) h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the mixed space of $F$ and $h$ a locally constant, compactly supported function on the finite adeles. Write $D$ for `AdelicBox.adelicBox F`, the set of adeles whose infinite component lies in the fundamental domain of the lattice basis of the mixed embedding and whose finite component is integral at every height-one prime of $\mathcal{O}_F$, and $\hat f(w) = \int_{\mathbb{A}_F} \psi(-(vw)) f(v)\, d\mu(v)$. Then $$\sum_{\xi \in F} f(\xi) - \mu(D)^{-1}\int_{\mathbb{A}_F} f \, d\mu = \mu(D)^{-1} \sum_{\xi \in F,\ \xi \neq 0} \hat f(\xi),$$ where $\mu(D)^{-1}$ means the inverse of the real number $\mu(D)$ viewed in $\mathbb{C}$, the sums are unconditional sums (`tsum`) over $F$ and over the subtype of non-zero elements, and $\xi$ is mapped into $\mathbb{A}_F$ by the structure map.
--
--   This is the adelic Poisson summation (Riemann–Roch) formula of Tate's thesis, rearranged so that the $\xi = 0$ Fourier coefficient $\hat f(0) = \int f \, d\mu$ appears separately as the mean value: the discrepancy between the sum of $f$ over $F$ and its mean equals the sum of the non-zero Fourier coefficients. In this shape it feeds the truncation and constant-term estimates for automorphic forms and the global results of Tate's theory, being cited for instance by the bound on $\sum f(\xi)$ minus its average in terms of archimedean height and by the characterisation of characters trivial on the norm-one ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        - ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∫ v, f v ∂μ
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
