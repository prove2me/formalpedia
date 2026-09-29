-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact
-- name    : NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/06e7660d-e822-588a-8f86-5bfe9172286c
-- title:
--   Character orthogonality over a compact subgroup of the finite adeles
-- statement:
--   Let $F$ be a number field, and let the finite adele ring $\mathbb{A}_F^f =$ `FiniteAdeleRing (𝓞 F) F` carry a measurable space structure that is the Borel structure of its topology. Let $\nu$ be an additive Haar measure on $\mathbb{A}_F^f$, let $\psi_f \colon \mathbb{A}_F^f \to \mathbb{C}$ be an additive character, that is, a homomorphism from the additive group of $\mathbb{A}_F^f$ to the multiplicative monoid of $\mathbb{C}$ (no continuity is assumed), let $K$ be an additive subgroup of $\mathbb{A}_F^f$ whose underlying set is compact, and let $\xi \in \mathbb{A}_F^f$. Then the Bochner integral of $z \mapsto \psi_f(\xi z)$ over the set $K$ with respect to $\nu$ equals the real number $\nu(K)$, viewed as a complex number via `ENNReal.toReal` and the coercion $\mathbb{R} \to \mathbb{C}$, in the case that $\psi_f(\xi z) = 1$ for every $z \in K$, and equals $0$ otherwise. The case distinction is made on the proposition $\forall z \in K,\ \psi_f(\xi z) = 1$, decided classically.
--
--   This is the orthogonality relation for additive characters on a compact group, in the shape needed for harmonic analysis on the finite adeles: the integral of $\psi_f(\xi\,\cdot)$ over a compact subgroup is the volume of the subgroup when the character is trivial on it, and vanishes otherwise. It is used in [`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq`](thm.html#NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq), where $K$ is an annihilator subgroup arising in the adelic Fourier inversion computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 := by sorry
