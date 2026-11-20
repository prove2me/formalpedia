-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_hasSum_charlierScaled
-- name    : LevyStochCalc.Probability.hasSum_charlierScaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:14:38.449177+00:00
-- url     : https://prove2.me/theorems/e6a2cd6e-e233-4807-991b-41fb33684b97
-- title:
--   hasSum charlierScaled
-- statement:
--   The source theorem `LevyStochCalc.Probability.hasSum_charlierScaled` is extracted from `LevyStochCalc.Probability.CharlierGenerating`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CharlierGenerating_F000

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

theorem _root_.LevyStochCalc.Probability.hasSum_charlierScaled (lam : ℝ) (n : ℕ) (t : ℂ) :
    HasSum (fun s : ℕ => t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ))
      (Complex.exp (-(lam * t)) * (1 + t) ^ n) := by sorry
