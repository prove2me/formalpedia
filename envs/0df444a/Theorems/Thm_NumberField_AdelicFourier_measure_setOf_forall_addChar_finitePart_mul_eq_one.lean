-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one
-- name    : NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/cc18af0b-da6a-5ea1-b121-e6c511f12b5e
-- title:
--   Haar volume of the annihilator of widehat𝒪_F
-- statement:
--   Let $F$ be a number field, let the finite adele ring $\mathbb A_F^f =$ `FiniteAdeleRing (𝓞 F) F` carry a measurable structure which is the Borel structure of its topology, and let $\nu$ be an additive Haar measure on $\mathbb A_F^f$. Let $\psi$ be an additive character of the adele ring $\mathbb A_F$ (presented as the product of the infinite and the finite adeles) with values in $\mathbb C$ which is global in the sense of the project's predicate: $\psi$ is trivial on the image of $F$ under the structure map $F \to \mathbb A_F$, continuous, and not the trivial character. Assume furthermore that $\psi$ is standard at the archimedean places, i.e. for every infinite adele $x$ one has $\psi(x,0) = e^{2\pi i \,\mathrm{Tr}}$, where $\mathrm{Tr}$ is the trace over $\mathbb R$ of the image of $x$ in the mixed space of $F$ under `InfiniteAdeleRing.ringEquiv_mixedSpace` and the exponential is `Real.fourierChar`. Then the $\nu$-measure of the set of finite adeles $w$ such that $\psi(0, w z) = 1$ for every finite adele $z$ all of whose components $z_v$ lie in the valuation ring $\mathcal O_v$ of $v$ (for all $v$ in the height-one spectrum of $\mathcal O_F$) equals the absolute norm of the different ideal $\mathfrak d_{F} =$ `differentIdeal ℤ (𝓞 F)`, cast into $[0,\infty]$, times $\nu$ of that set of integral finite adeles; the identity is one of extended non-negative reals.
--
--   This is the finite-adelic volume computation behind Fourier inversion on $\mathbb A_F^f$: the annihilator of $\widehat{\mathcal O}_F$ under a standard global additive character is $\mathfrak d_F^{-1} + \widehat{\mathcal O}_F$, a disjoint union of $\mathrm N(\mathfrak d_F)$ translates of $\widehat{\mathcal O}_F$, so the two volumes differ by the factor $\mathrm N(\mathfrak d_F)$. It is used in [`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq`](thm.html#NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq), where this constant appears in the finite-adelic double Fourier integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    ν {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      = (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ENNReal) * ν (integralFiniteAdeles (𝓞 F) F) := by sorry
