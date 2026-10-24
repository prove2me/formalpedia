-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_descend
-- name    : OAI.PiExponent.FormalInterpolation.finite_quotient_descend
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:55:52.438325+00:00
-- url     : https://prove2.me/theorems/10c9b7c1-c80a-40af-bd8f-72881d8dfe36
-- title:
--   Module finiteness descends to a larger ideal quotient
-- statement:
--   If a quotient of an algebra is finite as a module and its ideal is contained in a larger ideal, then the quotient by the larger ideal is also finite as a module.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

theorem OAI.PiExponent.FormalInterpolation.finite_quotient_descend
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I J : Ideal A) (hIJ : I ≤ J)
    (hfinite : Module.Finite R (A ⧸ I)) :
    Module.Finite R (A ⧸ J) := by sorry
