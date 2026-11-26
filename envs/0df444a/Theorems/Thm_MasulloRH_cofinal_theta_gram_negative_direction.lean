-- Prove2me | Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
-- name    : MasulloRH.cofinal_theta_gram_negative_direction
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T08:50:48.418706+00:00
-- url     : https://prove2.me/theorems/400ef67b-22ec-40f5-b8f4-ec1ca5a7b448
-- title:
--   A negative direction for the shifted real theta Gram matrix at arbitrarily large scales
-- statement:
--   For every natural lower bound N, there exist a scale n ≥ N, a number m, and m rational shifts such that K − (δ/2)E₀₀ has a negative direction, where δ = 1/(16(n+1)) and K is the real weighted Gram matrix of the given pulse and shifted theta functions. Equivalently, some real vector has a strictly negative quadratic form for this matrix. The statement asks for the existence of these shifts at arbitrarily large scales. The fixed-shift coefficient equivalence reduces the parent theorem to this open analytic assertion.
-- source:
--   Derived from the pulse, theta translates, Gram entries and threshold in MasulloRH.cofinal_exact_theta_gram_margin, https://prove2.me/theorems/b2ce922d-3f53-4192-b8a7-484fcd931614. This is the remaining existence assertion about the shifts in that exact-margin problem.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem MasulloRH.cofinal_theta_gram_negative_direction :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (y : Fin m → ℚ),
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x - (y i : ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x + 2*(1/4-δ)*|x|) : ℂ) * conj (u i x) * u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    ¬ (K - Matrix.single 0 0 (δ / 2)).PosSemidef := by sorry
