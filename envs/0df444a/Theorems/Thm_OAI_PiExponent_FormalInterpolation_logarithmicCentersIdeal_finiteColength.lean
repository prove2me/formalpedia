-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_finiteColength
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:04:24.362932+00:00
-- url     : https://prove2.me/theorems/b29415ae-9fa1-4603-9ef8-67215d3caa5c
-- title:
--   Finite colength of distinct logarithmic centers
-- statement:
--   For pairwise distinct centers and positive coordinate exponents, the quotient by the product of the logarithmic center ideals is finite-dimensional over Complex. The logarithmic coordinates form a triangular polynomial coordinate system; each local quotient by coordinate powers has finitely many monomial representatives, and distinct centers give comaximal local ideals for CRT. For K = 0 the product ideal is the unit ideal; for m = 0, distinctness restricts the possible centers and the same finite-quotient argument applies.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_finiteColength
    {m K : Nat} (c : Fin K → Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (hdist : ∀ j₁ j₂ : Fin K, j₁ ≠ j₂ → c j₁ ≠ c j₂) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ logarithmicCentersIdeal c T e) := by sorry
