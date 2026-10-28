-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fraction_field_finite_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.fraction_field_finite_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:46:28.14199+00:00
-- url     : https://prove2.me/theorems/db4fb8cb-99ba-4451-9877-c4d49698b238
-- title:
--   Finite transcendence degree of the target function field
-- statement:
--   The fraction field of the prime quotient of a polynomial ring in finitely many variables over ℂ has finite transcendence degree. It is generated as a field over ℂ by the images of the finitely many variables.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.fraction_field_finite_trdeg {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] : Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) < Cardinal.aleph0 := by sorry
