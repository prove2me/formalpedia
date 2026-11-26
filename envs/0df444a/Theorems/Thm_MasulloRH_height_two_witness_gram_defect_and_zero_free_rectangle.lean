-- Prove2me | Theorems.Thm_MasulloRH_height_two_witness_gram_defect_and_zero_free_rectangle
-- name    : MasulloRH.height_two_witness_gram_defect_and_zero_free_rectangle
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T14:32:27.203598+00:00
-- url     : https://prove2.me/theorems/0e972d7d-44d0-483d-b936-3171ed09194d
-- title:
--   An explicit negative height-two Gram direction and its zero-free zeta rectangle
-- statement:
--   For the published eleven rational theta coefficients and shifts at height two, the weighted residual energy is at most $200929077/20000000000$. In the corresponding twelve-dimensional real Gram matrix, subtract $1/96$ from the first diagonal entry. The vector formed by appending the negative witness coefficients to a leading one has squared norm $5930379/10000$. Its quadratic form is at most $-22212769/60000000000$, so its normalized Rayleigh quotient is at most $-22212769/35582274000000$. The same witness excludes Riemann zeta zeros for $43/80\le\operatorname{Re}s\le77/80$ and $|\operatorname{Im}s|\le2$, including the boundary.
-- source:
--   The finite-height instance of the Masullo cofinal Gram condition https://prove2.me/theorems/400ef67b-22ec-40f5-b8f4-ec1ca5a7b448 with its explicit rational witness https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness
import Mathlib.Data.Matrix.Basis
import Mathlib.NumberTheory.LSeries.RiemannZeta

open MasulloRH MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate

theorem MasulloRH.height_two_witness_gram_defect_and_zero_free_rectangle :
    let u : Fin 12 → ℝ → ℂ := Fin.cons (pulse 2) (fun i x => theta (x - HeightTwoWitness.shifts i))
    let K : Matrix (Fin 12) (Fin 12) ℝ := fun i j =>
      (∫ x : ℝ, (Real.exp (3/2*x + 11/24*|x|) : ℂ) * conj (u i x) * u j x).re
    let v : Fin 12 → ℝ := Fin.cons 1 (fun i => -(HeightTwoWitness.coeffsQ i : ℝ))
    energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts)
        ≤ 200929077/20000000000 ∧
      (∑ i, (v i)^2) = 5930379/10000 ∧
      (∑ i, ∑ j, v i * v j * (K - Matrix.single (0 : Fin 12) 0 (1/96 : ℝ) : Matrix (Fin 12) (Fin 12) ℝ) i j) ≤ -(22212769/60000000000) ∧
      ∀ s : ℂ, 43/80 ≤ s.re → s.re ≤ 77/80 → |s.im| ≤ 2 → riemannZeta s ≠ 0 := by sorry
