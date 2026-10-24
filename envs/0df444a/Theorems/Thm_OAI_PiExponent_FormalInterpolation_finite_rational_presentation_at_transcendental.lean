-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_rational_presentation_at_transcendental
-- name    : OAI.PiExponent.FormalInterpolation.finite_rational_presentation_at_transcendental
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:22:47.852456+00:00
-- url     : https://prove2.me/theorems/08570852-0975-474f-ba5f-764e8088f3db
-- title:
--   Finite rational presentation with a prescribed transcendental variable
-- statement:
--   Extend the algebraically independent singleton {y} to a transcendence basis S, and take K=k(S\{y}). Independence makes evaluation X↦y an embedding K(X)→E with image k(S). The extension E/k(S) is algebraic and essentially of finite type, hence finite. Relevant inspected Mathlib declarations are exists_isTranscendenceBasis_superset, IsTranscendenceBasis.isAlgebraic_field, RatFunc.liftAlgHom, Algebra.EssFiniteType.of_comp, and Algebra.finite_of_essFiniteType_of_isAlgebraic. This child removes the transcendence-basis and field-presentation work. The transcendence hypothesis excludes y=0 and algebraic y; in transcendence degree one the remaining basis is empty and K is the scalar subfield. No characteristic or algebraic-closedness assumption is needed.

import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.EssentialFiniteness

theorem OAI.PiExponent.FormalInterpolation.finite_rational_presentation_at_transcendental
    (k E : Type) [Field k] [Field E] [Algebra k E]
    [Algebra.EssFiniteType k E] (y : E) (hy : Transcendental k y) :
    ∃ (K : IntermediateField k E) (f : RatFunc K →ₐ[K] E),
      f RatFunc.X = y ∧
      (letI : Algebra (RatFunc K) E := f.toRingHom.toAlgebra
       FiniteDimensional (RatFunc K) E) := by sorry
