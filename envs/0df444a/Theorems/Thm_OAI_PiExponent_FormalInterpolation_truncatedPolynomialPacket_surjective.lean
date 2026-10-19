-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_surjective
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:04:47.92141+00:00
-- url     : https://prove2.me/theorems/fef84013-d60d-41d2-8985-3109154b54fc
-- title:
--   Realization of strict truncated packets
-- statement:
--   Every strict truncated packet is realized by a polynomial. At each center, use the triangular substitution defining the truncated jet to prescribe the finitely many requested coefficients, then glue the local polynomial data by CRT. The strict weighted inequality and hscale ensure each requested exponent survives in the local quotient by the nth coordinate-power ideal. For n = 0 or K = 0 the row domain is empty, so the assertion is vacuous.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_surjective
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (hr : ∃ i, r i ≠ 0) :
    ∀ n : Nat,
      ∀ f : InterpolationMatrix.Row K v0 theta w ((n : Real) * R) → Complex,
        ∃ P : MvPolynomial (Fin (m + 1)) Complex,
          truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = f := by sorry
