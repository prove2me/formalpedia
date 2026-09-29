-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet
-- name    : NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/a790d43b-0eb8-503e-9fe2-878e8b3a949d
-- title:
--   Adelic Poisson summation for pure tensors, unnormalised measure
-- statement:
--   Let $F$ be a number field, and equip its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` with a measurable space structure that is the Borel structure of its topology. Let $\mu$ be an additive Haar measure on $\mathbb{A}_F$, and let $\psi : \mathbb{A}_F \to \mathbb{C}$ be an additive character which is global in the sense of `IsGlobalAddChar`: it is trivial on the image of $F$ under the algebra map $F \to \mathbb{A}_F$, it is continuous, and it is not the trivial character. Let $f : \mathbb{A}_F \to \mathbb{C}$ lie in `pureTensorSet F`, i.e. there are a Schwartz function $g$ on the mixed space `mixedEmbedding.mixedSpace F` and a locally constant, compactly supported $h$ on the finite adele ring such that $f(x) = g(\iota_\infty(x_\infty))\,h(x_{\mathrm{fin}})$, where $\iota_\infty$ is the ring isomorphism from the infinite adeles to the mixed space. Then the unconditional sum of $f$ over the principal adeles equals $$\sum_{\xi \in F} f(\xi) = \bigl(\mu(B)_{\mathbb{R}}\bigr)^{-1} \sum_{\xi \in F} \widehat{f}(\xi),$$ the inverse being that of the real number $\mu(B)$ viewed in $\mathbb{C}$, where $B =$ `AdelicBox.adelicBox F` consists of the adeles whose archimedean part lies in the $\iota_\infty$-preimage of the fundamental domain of the lattice basis of `mixedEmbedding`, and whose finite part is integral at every height-one prime of $\mathcal{O}_F$, and where $\widehat{f}(w) = \int \psi(-(vw))\,f(v)\,d\mu(v)$.
--
--   This is the Poisson summation formula over $\mathbb{A}_F$ for Schwartz–Bruhat functions that are pure tensors, stated for an arbitrary additive Haar measure with the self-duality constant written as the inverse volume of the adelic box. It serves as the base case from which the summation formula for general Schwartz–Bruhat functions, and its translated form `tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral`, are obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
