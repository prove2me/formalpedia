-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
-- name    : NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/33bf1ba9-794c-5f68-a3a1-5ba304a3ff71
-- title:
--   Double annihilator of the integral finite adeles
-- statement:
--   Let $F$ be a number field, with adele ring realised as the product of the infinite adele ring $\mathbb{A}_{F,\infty}$ and the finite adele ring $\mathbb{A}_F^{f}$ of $\mathcal{O}_F$ in $F$, so that elements are written as pairs. Let $\psi$ be an additive character of the adele ring with values in $\mathbb{C}$ which is global in the sense that it is trivial on the image of $F$ under the structure map, is continuous, and is not the trivial character; assume further that $\psi$ is normalised at the infinite places, i.e. for every $x \in \mathbb{A}_{F,\infty}$ one has $\psi(x,0) = e^{2\pi i\,\mathrm{Tr}(x)}$, the trace being taken over $\mathbb{R}$ of the image of $x$ in the mixed space of $F$ under the canonical ring isomorphism. Let $u$ be a finite adele. Then the following are equivalent: (i) for every finite adele $w$ such that $\psi(0, w z) = 1$ for all $z$ in the set of integral finite adeles (those $z$ with $z_v$ in the ring of integers of the $v$-adic completion of $F$ for every $v$ in the height-one spectrum of $\mathcal{O}_F$), one has $\psi(0, u w) = 1$; (ii) $u$ is itself an integral finite adele, i.e. $u_v$ lies in the $v$-adic integers for every such $v$.
--
--   This is the self-duality of $\widehat{\mathcal{O}}_F \subset \mathbb{A}_F^{f}$ for the pairing $(u,w) \mapsto \psi(0,uw)$: the annihilator of the annihilator of the integral finite adeles is again the integral finite adeles, the intermediate annihilator being governed by the inverse different, as in the computation that the trace dual of the codifferent is $\mathcal{O}_F$ (the cited result [`NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual`](thm.html#NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual) identifies the annihilating elements of $F$ with the dual fractional ideal). It supplies the support statement needed by [`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq`](thm.html#NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq), the twofold Fourier transform on the finite adeles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (u : FiniteAdeleRing (𝓞 F) F) :
    (∀ w : FiniteAdeleRing (𝓞 F) F,
        (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1) → ψ (0, u * w) = 1)
      ↔ u ∈ integralFiniteAdeles (𝓞 F) F := by sorry
