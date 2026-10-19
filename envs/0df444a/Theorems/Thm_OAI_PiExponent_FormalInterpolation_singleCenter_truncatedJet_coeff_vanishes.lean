-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_singleCenter_truncatedJet_coeff_vanishes
-- name    : OAI.PiExponent.FormalInterpolation.singleCenter_truncatedJet_coeff_vanishes
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:14:47.422363+00:00
-- url     : https://prove2.me/theorems/b4ec46d8-f25f-4d6b-980e-e442e39282c6
-- title:
--   A truncated jet coefficient below the center ideal power cutoff vanishes
-- statement:
--   For one center, membership in the nth power of its logarithmic center ideal forces every truncated-jet coefficient with exponent in the strict weighted simplex of cutoff nR to vanish.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.singleCenter_truncatedJet_coeff_vanishes {m : Nat} (v0 theta : Real) (w : Fin m → Real) (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat) (c : Fin m → Complex) (hR : 0 < R) (he : ∀ i, 0 < e i) (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i) (n : Nat) (F : MvPolynomial (Fin (m + 1)) Complex) (hF : F ∈ logarithmicCenterIdeal c T e ^ n) (a : Fin (m + 1) → Nat) (ha : a ∈ OAI.PiExponent.strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) ((n : Real) * R)) : (truncatedPolynomialJet c T F).coeff (InterpolationMatrix.exponentVector a) = 0 := by sorry
