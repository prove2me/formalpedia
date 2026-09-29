-- Prove2me | Theorems.Thm_HairerSPDE_charFun_tilt_of_joint_gaussian
-- name    : HairerSPDE.charFun_tilt_of_joint_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T06:09:49.612178+00:00
-- url     : https://prove2.me/theorems/d2a27ff5-de4a-4e53-902b-a25ec03fc76c
-- title:
--   Cameron-Martin tilt characteristic function from joint Gaussianity
-- statement:
--   Let B, mu, h, h' be as in the Cameron-Martin density leaf, with h' measurable and square-integrable and reproducing L(h) against every dual, and assume the joint centred Gaussianity of each pair (L, h') in the form: every real combination aL + bh' pushes mu forward to the centred one-dimensional Gaussian with its own variance. Then the explicit density f(x) = exp(h'(x) - ||h'||^2/2) is mu-finite and its characteristic function is exp(i L(h) - C(L,L)/2). This is the finite-dimensional Gaussian exponential-tilt computation at the heart of Hairer Theorem 4.44 equation (4.14).
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Theorem 4.44 (Cameron-Martin) and equation (4.14), used in the proof of Proposition 4.45.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem charFun_tilt_of_joint_gaussian {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'rep : ∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h)
    (hjoint : ∀ (L : StrongDual ℝ B) (a b : ℝ),
      μ.map (fun x => a * L x + b * h' x) =
        gaussianReal 0 ((ProbabilityTheory.variance (fun x => a * L x + b * h' x) μ).toNNReal)) :
    IsFiniteMeasure (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2))))
    ∧ ∀ L : StrongDual ℝ B, charFunDual (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2)))) L = Complex.exp ((L h) * Complex.I - covarianceBilinDual μ L L / 2) := by sorry

end HairerSPDE
