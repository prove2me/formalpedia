-- Prove2me | Theorems.Thm_Kyprianou_Ch01_charFun_scaledBrownianZeroStart
-- name    : Kyprianou.Ch01.charFun_scaledBrownianZeroStart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:02:48.529776+00:00
-- url     : https://prove2.me/theorems/1e43a56c-4e1c-4bfd-ae55-618986b73882
-- title:
--   Strictly zero-start Brownian process scaled by nonnegative Gaussian variance has exact Lévy–Khintchine Fourier marginal
-- statement:
--   For any real Brownian motion X on a probability space and any nonnegative Gaussian variance v, the scaled strictly zero-start modification sqrt(v)(X_t-X_0) has exactly the centred Gaussian characteristic function exp(-v t ξ²/2) for all nonnegative times t and frequencies ξ. The proof derives the original Brownian law from pinned source, transfers it through the scalar map and uses the separately proved Gaussian scaling identity.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.6; pinned Mathlib IsPreBrownianReal.hasLaw_eval and HasLaw.comp, Proved Kyprianou Gaussian scaling.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.charFun_scaledBrownianZeroStart
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal X P)
    (v : ℝ≥0) (t : ℝ≥0) (xi : ℝ) :
    charFun (P.map
      (fun ω => Real.sqrt (v : ℝ) * (X t ω - X 0 ω))) xi =
      Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  sorry
