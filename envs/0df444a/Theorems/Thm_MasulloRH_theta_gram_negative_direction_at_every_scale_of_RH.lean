-- Prove2me | Theorems.Thm_MasulloRH_theta_gram_negative_direction_at_every_scale_of_RH
-- name    : MasulloRH.theta_gram_negative_direction_at_every_scale_of_RH
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T19:23:35.686038+00:00
-- url     : https://prove2.me/theorems/715a3f94-7bfb-5ac8-b99e-5b3029f35aef
-- title:
--   RH implies a strictly negative theta-Gram direction at every scale
-- statement:
--   Assuming the Riemann hypothesis, every scale n admits rational shifts whose real theta-Gram matrix fails positive semidefiniteness after subtracting half the prescribed margin in its first diagonal entry.
-- source:
--   Developed for the Masullo theta-window argument and the centered Möbius target. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem MasulloRH.theta_gram_negative_direction_at_every_scale_of_RH (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ (m : ℕ) (y : Fin m → ℚ),
    let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n) (fun i x => theta (x-(y i:ℝ)))
    let G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j =>
      ∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x
    let K : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := fun i j => (G i j).re
    ¬ (K-Matrix.single 0 0 (δ/2)).PosSemidef := by sorry
