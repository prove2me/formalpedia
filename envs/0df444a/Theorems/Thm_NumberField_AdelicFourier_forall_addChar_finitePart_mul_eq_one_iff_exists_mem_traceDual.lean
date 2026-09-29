-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
-- name    : NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/dd10f053-8a36-537a-85ef-e0fa0c3358c7
-- title:
--   Annihilator of the integral finite adeles is d⁻¹+widehat𝒪
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal O_F$, adele ring $\mathbb A_F$ presented as the product of the infinite adele ring and the finite adele ring, and let $\psi\colon\mathbb A_F\to\mathbb C$ be an additive character satisfying `IsGlobalAddChar`, i.e. $\psi$ is trivial on the image of $F$ under the structure map $F\to\mathbb A_F$, continuous, and not identically $1$. Assume further that $\psi$ is standard at the infinite places: for every $x$ in the infinite adele ring, $\psi(x,0)$ equals the value of `Real.fourierChar` at the trace over $\mathbb R$ of the image of $x$ under the identification of the infinite adele ring with the mixed space $\mathbb R^{r_1}\times\mathbb C^{r_2}$. Let $w$ be a finite adele. The theorem asserts the equivalence of: (i) $\psi(0,wz)=1$ for every finite adele $z$ lying in `integralFiniteAdeles`, that is, every $z$ whose component at each $v$ in the height-one spectrum of $\mathcal O_F$ lies in the valuation ring $\mathcal O_v$ of the $v$-adic completion; and (ii) there exists $r\in F$ belonging to the trace dual `FractionalIdeal.dual ℤ ℚ 1` of the unit fractional ideal (the inverse different $\mathfrak d_F^{-1}$), viewed as a fractional ideal of $\mathcal O_F$, such that $w-\iota(r)$ is again integral at every finite place, where $\iota\colon F\to\mathbb A_F^{f}$ is the structure map.
--
--   This identifies the annihilator of $\widehat{\mathcal O}_F$ for the self-pairing $(w,z)\mapsto\psi(0,wz)$ of the finite adele ring as $\mathfrak d_F^{-1}+\widehat{\mathcal O}_F$, the adelic form of the statement that the conductor of a standard additive character at a finite place is the local different. It is used in the adelic Fourier theory of this development — compactness and openness of the annihilator, local constancy and compact support of Fourier integrals over the finite adeles, and the computation of the level of the local Tate character in terms of the different ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (w : FiniteAdeleRing (𝓞 F) F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
          ∧ w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F := by sorry
