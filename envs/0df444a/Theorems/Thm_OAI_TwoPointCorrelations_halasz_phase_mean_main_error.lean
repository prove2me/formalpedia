-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_phase_mean_main_error
-- name    : OAI.TwoPointCorrelations.halasz_phase_mean_main_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:25.065205+00:00
-- url     : https://prove2.me/theorems/9d98e6ec-d4f7-4cfa-a87e-8e94229f6d63
-- title:
--   The phase mean of a multiplicative function equals N^{−it}/(1−it) times its unit main term, up to the correction mass
-- statement:
--   Let $F$ be multiplicative (on coprime positive arguments) with $F(1)=1$, $t$ real and $N$ natural. Then
--
--   $$\Big|\Phi_F(t,N)-\frac{N^{-it}}{1-it}\,\mathcal M_F(N)\Big|\le9(1+|t|)\sum_{d=1}^N\big|c_F(d)\big|,$$
--
--   where $\Phi_F(t,N)=\sum_{n=1}^NF(n)e^{-it\log n}$ (`halaszPhaseMean`), $c_F$ = `halaszUnitCorrection F` is the multiplicative function built from prime powers by `fromPrimePowers (halaszUnitCorrectionLocal F)` (see the bundle), and $\mathcal M_F(N)=N\sum_{d=1}^Nc_F(d)/d$ (`halaszUnitMain`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_phase_mean_main_error`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem halasz_phase_mean_main_error (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N‖ ≤
      9 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  sorry

end OAI.TwoPointCorrelations
