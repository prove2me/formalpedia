-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
-- name    : NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9d4d751b-f46a-5f6e-b3e0-2d37597c97aa
-- title:
--   Adelic Fourier inversion for pure tensors
-- statement:
--   Let $F$ be a number field, let its adele ring $\mathbb{A}_F = \mathbb{A}_{F,\infty} \times \mathbb{A}_F^{f}$ carry a measurable structure which is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi : \mathbb{A}_F \to \mathbb{C}^\times$ be an additive character which is global in the sense of `IsGlobalAddChar`: it is trivial on the image of $F$ under the structure map $F \to \mathbb{A}_F$, it is continuous, and it is not the trivial character. Let $f : \mathbb{A}_F \to \mathbb{C}$ lie in `pureTensorSet F`, i.e. $f(x) = g(x_\infty)\,h(x_{\mathrm{f}})$ for some Schwartz function $g$ on the mixed space of $F$ (the infinite component being transported along `InfiniteAdeleRing.ringEquiv_mixedSpace`) and some locally constant, compactly supported $h$ on the finite adele ring of $\mathcal{O}_F$. Then, for every $x \in \mathbb{A}_F$, with $\widehat{u}(w) = \int_{\mathbb{A}_F} \psi(-(vw))\,u(v)\,d\mu(v)$, one has $$\widehat{\widehat{f}}(x) = \mu(B)^2\, f(-x),$$ where $B$ is the adelic box consisting of the adeles whose infinite part lies in the preimage of the fundamental domain of the lattice basis of the mixed space and whose finite part is integral at every height-one prime of $\mathcal{O}_F$, and $\mu(B)$ is taken as a real number.
--
--   This is the Fourier inversion formula for $\mathbb{A}_F$, in the normalisation in which the same character $\psi$ is used for both transforms and the minus sign sits in the kernel, restricted to the pure tensors $g \otimes h$ generating the adelic Schwartz–Bruhat space. It is the generating-set case from which the inversion formula for the whole Schwartz–Bruhat span ([`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq`](thm.html#NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq)) is obtained, and it is used in producing Schwartz–Bruhat functions with prescribed positivity of their integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) (x : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fourierIntegral ψ μ f) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * f (-x) := by sorry
