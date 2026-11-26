-- Prove2me | Theorems.Thm_MasulloRH_height_two_shared_grid_enclosures
-- name    : MasulloRH.height_two_shared_grid_enclosures
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T09:20:55.053802+00:00
-- url     : https://prove2.me/theorems/a1982f8d-9d4a-4b3f-88ac-3a2cdaee2ead
-- title:
--   Shared rational value enclosures for the eleven-term height-two theta witness
-- statement:
--   For the eleven coefficients and shifts of the published height-two witness, take \(D=8192\) and divide \([-4,4]\) into \(8D\) cells of width \(h=1/D\). Write \(s_i=D y_i\). There are rational pulse centers \(P_j\), pulse radii \(R_j\), weight bounds \(W_j\), and a common table of rational theta centers \(T_k\) and radii \(U_k\). On cell \(j\), they enclose the canonical pulse and weight, and on cell \(j-s_i\) they enclose the canonical theta translate. They satisfy
--
--   \[
--    \sum_{j<8D} hW_j\left(\left|P_j-\sum_i a_iT_{j-s_i}\right|+R_j+
--                       \sum_i |a_i|U_{j-s_i}\right)^2\leq\frac1{100}.
--   \]
--
--   The pulse is the scale-two normalized Gaussian and the weight is \(\exp(3x/2+11|x|/24)\). This finite table would supply the compact part of the height-two energy certificate.
-- source:
--   The eleven rational coefficients and shifts come from sflicht’s published MasulloRH_HeightTwoWitness, https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d . This separate uniform-grid calculation uses the accepted reflection and truncation identities at https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe and https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 .

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.height_two_shared_grid_enclosures :
    let h : ℝ := 1/8192
    let e (k : ℤ) := -4 + (k : ℝ) * h
    let s : Fin 11 → ℤ := ![-3072,-2048,1024,3072,6144,8192,11264,14336,16384,18432,19456]
    ∃ (P R W : ℕ → ℚ) (T U : ℤ → ℚ),
      (∀ (j : ℕ), j < 65536 → 0 ≤ (W j : ℝ) ∧ ∀ x ∈ Icc (e j) (e ((j : ℤ)+1)),
        ‖pulse 2 x - (P j : ℂ)‖ ≤ (R j : ℝ) ∧
          Real.exp (2*(3/4)*x + 2*(11/48)*|x|) ≤ (W j : ℝ)) ∧
      (∀ (j : ℕ), j < 65536 → ∀ i : Fin 11, ∀ z ∈ Icc (e ((j : ℤ)-s i)) (e ((j : ℤ)-s i+1)),
        ‖theta z - (T ((j : ℤ)-s i) : ℂ)‖ ≤ (U ((j : ℤ)-s i) : ℝ)) ∧
      (let A (j : ℕ) := ‖(P j : ℂ) - ∑ i, HeightTwoWitness.coeffs i * (T ((j : ℤ)-s i) : ℂ)‖ +
          ((R j : ℝ) + ∑ i, ‖HeightTwoWitness.coeffs i‖ * (U ((j : ℤ)-s i) : ℝ))
       ∑ j ∈ Finset.range 65536, h * ((W j : ℝ) * A j ^ 2) ≤ 1/100) := by sorry
