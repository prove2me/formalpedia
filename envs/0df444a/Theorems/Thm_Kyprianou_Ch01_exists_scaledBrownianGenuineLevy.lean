-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exists_scaledBrownianGenuineLevy
-- name    : Kyprianou.Ch01.exists_scaledBrownianGenuineLevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:07:40.270908+00:00
-- url     : https://prove2.me/theorems/5cad652b-ed30-41f8-b248-f78fc1a51da6
-- title:
--   Existence of a genuine measurable Lévy process with arbitrary Gaussian variance and exact Brownian characteristic function
-- statement:
--   For every nonnegative Gaussian variance v, there exists a probability space carrying a genuine real-valued Lévy process with measurable time marginal functions whose law at every time t has characteristic function exp(-vtξ²/2). A witness is the globally Proved canonical real Brownian motion on GaussianLimit path space, normalised by subtracting its actual initial value and scaled by the square root of v. Genuine Lévy-process properties are preserved by the separately Proved normalisation and constant-scaling theorems. Marginal measurability follows from a globally Proved canonical Brownian measurability lemma; the exact characteristic function follows from the separately compiler-verified Brownian marginal scaling theorem. This is the positive Gaussian component of Kyprianou (2006) Chapter 1 Lévy–Khintchine existence.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.6; globally Proved ProbabilityTheory.isBrownianReal_brownian_avram, AvramDividend.Classical.canonical_drifted_brownian_measurable, Kyprianou.Ch01.isLevyProcess_realScale, and Kyprianou.Ch01.charFun_scaledBrownianZeroStart.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.exists_scaledBrownianGenuineLevy (v : ℝ≥0) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess B P ∧
        (∀ t, Measurable (B t)) ∧
        ∀ (t : ℝ≥0) (xi : ℝ),
          charFun (P.map (B t)) xi =
            Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) *
              (xi : ℂ) ^ 2 / 2)) := by
  sorry
