-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
-- name    : OAI.PiExponent.FormalInterpolation.exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:58:10.20414+00:00
-- url     : https://prove2.me/theorems/89bbaf2c-0982-4da8-a400-b63dbcb52a80
-- title:
--   Trdeg-one essentially finite-type fields are finite over a simple transcendental adjunction
-- statement:
--   Let $K\subseteq E$ be a field extension that is essentially of finite type and of transcendence degree one. Then there exists an element $t\in E$, transcendental over $K$, such that $E$ is a finite-dimensional vector space over the simple transcendental extension $K(t)=K\langle t\rangle$.
--
--   This is the standard one-variable function-field presentation: a transcendence basis has cardinality one, the adjunction of that element is purely transcendental of degree one, and essential finite type upgrades algebraicity of $E/K(t)$ to finite dimensionality (Mathlib `Algebra.finite_of_essFiniteType_of_isAlgebraic`).
-- source:
--   Stacks Project Tag 030G / Mathlib FinTrdeg + AlgebraicIndependent.TranscendenceBasis; used as the finite-presentation bridge for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite

import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.EssentialFiniteness

open IntermediateField

theorem OAI.PiExponent.FormalInterpolation.exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] (htrdeg : Algebra.trdeg K E = 1) :
    ∃ t : E, Transcendental K t ∧
      Module.Finite (IntermediateField.adjoin K ({t} : Set E)) E := by sorry
