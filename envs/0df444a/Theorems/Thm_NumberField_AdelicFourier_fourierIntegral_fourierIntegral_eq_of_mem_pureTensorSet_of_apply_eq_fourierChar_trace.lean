-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
-- name    : NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9a7b8852-f14e-5446-8d62-da5f3de88ecc
-- title:
--   Adelic Fourier inversion for pure tensors
-- statement:
--   Let $F$ be a number field, its adele ring $\mathbb{A}_F = \mathbb{A}_{F,\infty}\times\mathbb{A}_F^{\mathrm{f}}$ carrying a measurable space structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi\colon\mathbb{A}_F\to\mathbb{C}$ be an additive character which is global in the sense that it is trivial on the image of $F$ under the structure map $F\to\mathbb{A}_F$, continuous, and not the trivial character, and assume in addition that its archimedean part is the standard one: for every $x\in\mathbb{A}_{F,\infty}$, $\psi(x,0)=e^{2\pi i\,\mathrm{Tr}_{\mathbb{R}}(\bar x)}$, where $\bar x$ is the image of $x$ in the mixed space $F\otimes_{\mathbb{Q}}\mathbb{R}\simeq\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ under `InfiniteAdeleRing.ringEquiv_mixedSpace` and $\mathrm{Tr}_{\mathbb{R}}$ is the algebra trace of the mixed space over $\mathbb{R}$. Let $f\colon\mathbb{A}_F\to\mathbb{C}$ be a pure tensor, i.e. $f(x)=g(\bar{x_\infty})\,h(x_{\mathrm{f}})$ for some Schwartz function $g$ on the mixed space and some locally constant $h$ of compact support on the finite adeles. With $\widehat{f}(w)=\int_{\mathbb{A}_F}\psi(-vw)f(v)\,d\mu(v)$, the assertion is that for every $x\in\mathbb{A}_F$,
--   $$\widehat{\widehat{f}}(x)=\big(\mu(B)\big)^2\,f(-x),$$
--   where $B\subset\mathbb{A}_F$ is the adelic box consisting of those $x$ whose archimedean component lies in the preimage of the fundamental domain of the lattice basis of $\mathcal{O}_F$ in the mixed space and whose finite component is integral at every height-one prime of $\mathcal{O}_F$, and $\mu(B)$ is taken as a real number and then regarded as a complex number.
--
--   This is the Fourier inversion formula of Tate's thesis in the form needed for the adelic Schwartz–Bruhat space, restricted to pure tensors and to characters whose archimedean component is $e^{2\pi i \mathrm{Tr}}$; the normalising constant is the square of the $\mu$-volume of the adelic box, with no separate discriminant factor. It feeds the version [`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet`](thm.html#NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet) stated without the archimedean normalisation hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) (x : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fourierIntegral ψ μ f) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * f (-x) := by sorry
