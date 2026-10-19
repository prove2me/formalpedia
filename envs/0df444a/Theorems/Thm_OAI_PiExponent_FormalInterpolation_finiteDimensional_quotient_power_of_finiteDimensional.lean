-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_quotient_power_of_finiteDimensional
-- name    : OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_power_of_finiteDimensional
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:08:48.892978+00:00
-- url     : https://prove2.me/theorems/11e97e9c-6697-41b6-8503-cfa96f9ddcbd
-- title:
--   Finite dimensionality of a power-ideal quotient
-- statement:
--   If the quotient of the multivariate complex polynomial ring by an ideal is finite-dimensional, then its quotient by any natural power of that ideal is finite-dimensional.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_power_of_finiteDimensional
    {m : Nat} (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I))
    (s : Nat) :
    FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I ^ s) := by sorry
