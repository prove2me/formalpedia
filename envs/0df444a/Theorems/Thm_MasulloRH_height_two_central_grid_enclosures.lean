-- Prove2me | Theorems.Thm_MasulloRH_height_two_central_grid_enclosures
-- name    : MasulloRH.height_two_central_grid_enclosures
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T09:48:11.296837+00:00
-- url     : https://prove2.me/theorems/44743777-9b41-5194-84da-ff2782e96168
-- title:
--   The remaining central theta table for the eleven-term height-two witness
-- statement:
--   Use the eleven rational coefficients and shifts of the height-two witness. Give rational disk enclosures for theta on each of the 36,864 intervals of width \(1/8192\) in \([-3,3/2]\). Give rational pulse enclosures and upper bounds for the weight on the 65,536 cells of \([-4,4]\). Extend the central theta table with constant center zero and radius \(2^{-64}\) on the two outer regions. The signed sum of centers, plus the pulse radius and absolute-coefficient-weighted theta radii, gives an upper bound \(A_j\) on the residual magnitude. The sum of \(W_j A_j^2/8192\) over all compact cells must be at most \(1/100\). The cell coordinates, complex casts and sum are specified in the Lean statement.
-- source:
--   The explicit rational witness is https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d . This is a component of https://prove2.me/theorems/a1982f8d-9d4a-4b3f-88ac-3a2cdaee2ead .

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.height_two_central_grid_enclosures :
    let h : ℝ := 1/8192
    let e (k : ℤ) := -4 + (k : ℝ) * h
    let s : Fin 11 → ℤ := ![-3072,-2048,1024,3072,6144,8192,11264,14336,16384,18432,19456]
    ∃ (P R W : ℕ → ℚ) (C D : ℤ → ℚ),
      (∀ (j : ℕ), j < 65536 → 0 ≤ (W j : ℝ) ∧ ∀ x ∈ Icc (e j) (e ((j : ℤ)+1)),
        ‖pulse 2 x - (P j : ℂ)‖ ≤ (R j : ℝ) ∧
          Real.exp (2*(3/4)*x + 2*(11/48)*|x|) ≤ (W j : ℝ)) ∧
      (∀ k : ℤ, 8192 ≤ k → k < 45056 → ∀ z ∈ Icc (e k) (e (k+1)),
        ‖theta z - (C k : ℂ)‖ ≤ (D k : ℝ)) ∧
      (let T (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 0 else C k
       let U (k : ℤ) : ℚ := if k < 8192 ∨ 45056 ≤ k then 1/(2:ℚ)^64 else D k
       let A (j : ℕ) := ‖(P j : ℂ) - ∑ i, HeightTwoWitness.coeffs i * (T ((j : ℤ)-s i) : ℂ)‖ +
          ((R j : ℝ) + ∑ i, ‖HeightTwoWitness.coeffs i‖ * (U ((j : ℤ)-s i) : ℝ))
       ∑ j ∈ Finset.range 65536, h * ((W j : ℝ) * A j ^ 2) ≤ 1/100) := by sorry
