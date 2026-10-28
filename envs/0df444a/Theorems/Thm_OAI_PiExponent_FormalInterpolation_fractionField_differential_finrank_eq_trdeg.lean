-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fractionField_differential_finrank_eq_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:55:23.602815+00:00
-- url     : https://prove2.me/theorems/41b0e3a0-2b1e-496e-8852-668206a9ca64
-- title:
--   Fraction field differential dimension equals transcendence degree
-- statement:
--   The dimension over the fraction field of its Kähler differential space over ℂ equals the transcendence degree of this finitely generated characteristic-zero field extension.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) =
      Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) := by sorry
