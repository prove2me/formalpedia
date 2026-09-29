-- Prove2me | Theorems.Thm_HairerSPDE_charFunDual_withDensity_exp_of_representer
-- name    : HairerSPDE.charFunDual_withDensity_exp_of_representer
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T12:22:36.87962+00:00
-- url     : https://prove2.me/theorems/2284de01-01c8-4172-8647-f08f4bf30547
-- title:
--   Characteristic function of the Cameron-Martin density
-- statement:
--   **Characteristic function of the Cameron-Martin density.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, $h \in B$, and $h^* \in L^2(B,\mu)$ a reproducing element with $\int h^*\ell\,d\mu = \ell(h)$ for all $\ell \in B^*$ and lying in the closed span $R_\mu$ of the duals. Then the explicit density $f(x) = \exp(h^*(x) - \tfrac12\|h^*\|_{L^2}^2)$ is $\mu$-finite and its characteristic function is $\widehat{f\mu}(\ell) = \exp(i\ell(h) - C_\mu(\ell,\ell)/2)$. This is the Gaussian moment-generating computation at the heart of Hairer's Theorem 4.44 (equation (4.14)): the exponent combines with $i\ell$ and the reproducing identity $\int h^*\ell\,d\mu = \ell(h)$ picks out exactly the translate's characteristic function.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Theorem 4.44 (Cameron-Martin) and equation (4.14), used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem charFunDual_withDensity_exp_of_representer {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'rep : ∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h)
    (h'orth : (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0)) :
    IsFiniteMeasure (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2))))
    ∧ ∀ L : StrongDual ℝ B, charFunDual (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2)))) L = Complex.exp ((L h) * Complex.I - covarianceBilinDual μ L L / 2) := by sorry

end HairerSPDE
