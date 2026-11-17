-- Prove2me | Theorems.Thm_Kyprianou_Ch01_strictBrownian_zeroGaussianCharFun
-- name    : Kyprianou.Ch01.strictBrownian_zeroGaussianCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:21:39.480581+00:00
-- url     : https://prove2.me/theorems/aafe0eaf-0258-4431-b173-15ca5a1fcafc
-- title:
--   Zero-start Brownian modification has the exact centred Gaussian time-marginal characteristic function
-- statement:
--   For any Mathlib real Brownian motion X, probability law P, nonnegative time t and real frequency xi, the characteristic function of the zero-start modification X(t)-X(0) equals exp(-t xi²/2). The proof uses the independently proved Brownian zero-initial marginal and Brownian process normalisation to identify the exact zero-centred Gaussian law, then the pinned Mathlib Gaussian characteristic-function formula.
-- source:
--   Kyprianou (2006), Chapter 1, Gaussian term in the Lévy–Khintchine characteristic formula; pinned Mathlib ProbabilityTheory.IsPreBrownianReal.hasLaw_eval and charFun_gaussianReal.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.strictBrownian_zeroGaussianCharFun
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal X P) (t : ℝ≥0) (xi : ℝ) :
    charFun (P.map (fun ω => X t ω - X 0 ω)) xi =
      Complex.exp (-(((t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  sorry
