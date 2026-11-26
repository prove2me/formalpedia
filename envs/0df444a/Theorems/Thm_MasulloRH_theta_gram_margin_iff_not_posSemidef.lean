-- Prove2me | Theorems.Thm_MasulloRH_theta_gram_margin_iff_not_posSemidef
-- name    : MasulloRH.theta_gram_margin_iff_not_posSemidef
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:50:54.846875+00:00
-- url     : https://prove2.me/theorems/74fd242f-b84e-519f-ab8e-8331c9481531
-- title:
--   Rational theta coefficients attain the strict margin exactly when the shifted real Gram matrix has a negative direction
-- statement:
--   Fix a natural scale n, a finite number m of translates, and rational shifts y. Let δ = 1/(16(n+1)), and use the pulse as the zeroth function, followed by the m shifted theta functions. Let K be the real part of their exact weighted Gram matrix, with the weight and ordering in the parent theorem. There exist rational complex coefficients attaining energy strictly below δ/2 if and only if K − (δ/2)E₀₀ has a negative direction. Here E₀₀ has a single unit entry at (0,0). This holds for repeated shifts and for singular Gram matrices.
-- source:
--   Derived from the pulse, theta translates, Gram entries and threshold in MasulloRH.cofinal_exact_theta_gram_margin, https://prove2.me/theorems/b2ce922d-3f53-4192-b8a7-484fcd931614. The equivalence follows from reality of the integrands, the real quadratic-form criterion, and density of rational vectors.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem MasulloRH.theta_gram_margin_iff_not_posSemidef (n m : ℕ) (y : Fin m → ℚ) :
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x - (y i : ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x + 2*(1/4-δ)*|x|) : ℂ) * conj (u i x) * u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    (∃ a : Fin m → ℚ × ℚ,
      let d : Fin (m+1) → ℂ := Fin.cons 1 (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
      (∑ i, ∑ j, conj (d i) * d j * G i j).re < δ / 2) ↔ ¬ (K - Matrix.single 0 0 (δ / 2)).PosSemidef := by sorry
