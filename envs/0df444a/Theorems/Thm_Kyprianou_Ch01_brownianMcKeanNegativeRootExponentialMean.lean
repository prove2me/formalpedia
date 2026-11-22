-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianMcKeanNegativeRootExponentialMean
-- name    : Kyprianou.Ch01.brownianMcKeanNegativeRootExponentialMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:37:18.696602+00:00
-- url     : https://prove2.me/theorems/05844a29-ebcf-4d8f-9fb5-3703a9c6a4a0
-- title:
--   Discounted negative McKean root exponential has expectation one at every Brownian time
-- statement:
--   Use Proved Kyprianou.Ch01.brownianRealExponentialMartingale with theta=−phi and s=0, t arbitrary. The already Proved mckeanBrownianPhiHarmonicRoot gives psi=sigma² theta²/2+gamma theta=q. Since IsLinearBrownian implies IsLevyProcess X P with the proved deterministic start_zero field, M0=1 for all sample points, so the martingale's set-integral identity at the whole space gives E[exp(−phi X_t−qt)]=1. The original integrability is inherited from the Proved martingale. This is the exact exponential moment required to transport affine-exponential majorants under the Brownian transition semigroup without local-time calculus.
-- source:
--   Kyprianou (2006) Ch 1 Theorem 1.13, negative-root exponential martingale.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
import Theorems.Thm_Kyprianou_Ch01_mckeanBrownianPhiHarmonicRoot
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianMcKeanNegativeRootExponentialMean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) :
    let phi := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    Integrable (fun ω => Real.exp (-phi * X t ω - q * (t : ℝ))) P ∧
      (∫ ω, Real.exp (-phi * X t ω - q * (t : ℝ)) ∂P) = 1 := by sorry
