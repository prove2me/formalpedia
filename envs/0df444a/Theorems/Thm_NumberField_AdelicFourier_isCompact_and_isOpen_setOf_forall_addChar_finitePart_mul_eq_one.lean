-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
-- name    : NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/2d58c3e8-5d2f-5778-8ccd-2628d1552ebb
-- title:
--   Compactness and openness of the annihilator of widehat𝒪_F
-- statement:
--   Let $F$ be a number field, and let $\psi$ be an additive character of the adele ring $\mathbb A_F$ of $F$ (realised as the product of the infinite adele ring and the finite adele ring of $\mathcal O_F$) with values in $\mathbb C$. Assume $\psi$ is a global additive character in the sense that $\psi(\alpha)=1$ for every $\alpha$ in the image of $F$ under the structure map $F\to\mathbb A_F$, that $\psi$ is continuous, and that $\psi\neq 1$; assume moreover that $\psi$ is standard at the archimedean places, i.e. for every $x$ in the infinite adele ring one has $\psi(x,0)=e^{2\pi i\,\mathrm{Tr}(x)}$, where $\mathrm{Tr}$ is the trace over $\mathbb R$ of the image of $x$ under the ring isomorphism from the infinite adele ring onto the mixed space of $F$, and $e^{2\pi i(\cdot)}$ is `Real.fourierChar`. Then the set of finite adeles $w$ such that $\psi(0,wz)=1$ for every finite adele $z$ with $z_v\in\mathcal O_v$ at every $v$ in the height-one spectrum of $\mathcal O_F$ is both compact and open in the finite adele ring.
--
--   This is the topological half of the computation of the annihilator of the integral finite adeles $\widehat{\mathcal O}_F$ under a standard global additive character, the annihilator being the inverse different translate $\mathfrak d_F^{-1}+\widehat{\mathcal O}_F$. It is used in the adelic Fourier theory of this development: in the Fourier inversion formula over the finite adeles, in the statement that the finite Fourier transform of a locally constant compactly supported function is again locally constant with compact support, and in the global theory of Tate's zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by sorry
