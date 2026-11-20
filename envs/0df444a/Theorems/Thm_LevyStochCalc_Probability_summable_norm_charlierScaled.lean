-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_summable_norm_charlierScaled
-- name    : LevyStochCalc.Probability.summable_norm_charlierScaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:14:55.78063+00:00
-- url     : https://prove2.me/theorems/d859ca50-0215-4955-8443-f33e9ca81821
-- title:
--   summable norm charlierScaled
-- statement:
--   The source theorem `LevyStochCalc.Probability.summable_norm_charlierScaled` is extracted from `LevyStochCalc.Probability.CharlierGenerating`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Charlier_F001
import Definitions.Def_LevyStochCalc_Probability_Charlier_F002
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Charlier polynomials

At a natural argument `n` the Charlier polynomials with parameter `lam` (the mean of the Poisson
law that makes them orthogonal) are generated over `ℂ` by
`e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)`, obtained by induction on `n`: the value
`C_s(0; lam) = (-lam) ^ s` matches the exponential series at `n = 0`, and the forward difference
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)` turns the step into an index shift, which on the
generating side multiplies by `1 + t`. The same induction, run on the bound
`|T_(s+1)(n + 1)| ≤ |T_(s+1)(n)| + |t| |T_s(n)|` for the terms `T_s(n) = (t ^ s / s!) C_s(n; lam)`
and started from the exponential series at `n = 0`, shows that the series is absolutely summable
at every natural argument.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_zero_arg` — `C_s(0; lam) = (-lam) ^ s`.
* `LevyStochCalc.Probability.hasSum_charlierScaled` —
  `e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_charlierScaled` — absolute summability of
  `t ^ s / s! · C_s(n; lam)` at every natural argument.
-/

namespace LevyStochCalc.Probability

open Finset

theorem _root_.LevyStochCalc.Probability.summable_norm_charlierScaled (lam : ℝ) (n : ℕ) (t : ℂ) :
    Summable fun s : ℕ => ‖t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ)‖ := by sorry
