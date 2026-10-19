-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_finiteDimensional
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_finiteDimensional
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:10:06.959045+00:00
-- url     : https://prove2.me/theorems/c5c48ecc-2e92-47a3-a155-3990a2f495c3
-- title:
--   Finite dimensionality of a logarithmic center quotient
-- statement:
--   For a center and positive coordinate exponents, the quotient by its logarithmic center ideal is finite-dimensional over Complex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_finiteDimensional
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ logarithmicCenterIdeal c T e) := by sorry
