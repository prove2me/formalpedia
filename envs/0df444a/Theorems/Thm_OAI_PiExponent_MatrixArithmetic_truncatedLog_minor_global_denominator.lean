-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_truncatedLog_minor_global_denominator
-- name    : OAI.PiExponent.MatrixArithmetic.truncatedLog_minor_global_denominator
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T17:19:49.614923+00:00
-- url     : https://prove2.me/theorems/d7282896-c90f-4fbd-8651-21dcbebce2b8
-- title:
--   Global denominator for a nonzero truncated-log coefficient minor
-- statement:
--   For any finite square matrix of truncated-log monomial coefficients with nonzero determinant, the total transverse row exponents do not exceed the total column exponents coordinatewise. The product of the corresponding rational-center denominator powers and column logarithm-lcm powers clears its determinant to a Gaussian integer.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.truncatedLog_minor_global_denominator
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (T : Fin m → ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ)
    (hdet : (Matrix.of (fun r c : ι =>
      OAI.PiExponent.InterpolationMatrix.entry
        (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
        (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))
        (j r) (s r) (b r) (h c) (a c))).det ≠ 0) :
    (∀ i, (∑ r, b r i) ≤ ∑ c, a c i) ∧
      ∃ g : GaussianInt,
        ((∏ i, (q i ^ ((∑ c, a c i) - (∑ r, b r i)) *
          Nat.lcmUpto (T i) ^ (∑ c, a c i)) : ℕ) : ℂ) *
          (Matrix.of (fun r c : ι =>
            OAI.PiExponent.InterpolationMatrix.entry
              (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
              (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))
              (j r) (s r) (b r) (h c) (a c))).det = (g : ℂ) := by sorry
