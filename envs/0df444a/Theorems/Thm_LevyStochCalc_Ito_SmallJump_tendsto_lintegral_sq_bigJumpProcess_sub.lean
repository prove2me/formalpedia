-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SmallJump_tendsto_lintegral_sq_bigJumpProcess_sub
-- name    : LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:15:01.99029+00:00
-- url     : https://prove2.me/theorems/0b291323-67e0-4f60-a05c-f190c40ab43b
-- title:
--   tendsto lintegral sq bigJumpProcess sub
-- statement:
--   The source theorem `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` is extracted from `LevyStochCalc.Ito.SmallJumpProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SmallJumpProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Removing the small jumps of a jump diffusion

For a jump diffusion `X` and an antitone family `A : ℕ → Set E` of mark sets whose intersection
is `ν`-null, the *big-jump process* is the path with the compensated integral of the jump
coefficient over `A m` subtracted coordinatewise. The subtracted term is the everywhere-càdlàg
modification of the compensated integral of a mark cut, so its `L²` size is the energy carried
by `A m` and vanishes as `m → ∞`; the big-jump processes therefore converge to the path at every
fixed nonnegative time in `L²`, almost surely along a subsequence, at almost every time of a
bounded window along a subsequence, and — after composing with a `C²` function of time and
state — pathwise along that subsequence.

## Main definitions

* `LevyStochCalc.Ito.SmallJump.JumpIntegrand` — the filtration and admissibility data with
  which the coordinates of the jump coefficient along a path are integrated against `Ñ`.
* `LevyStochCalc.Ito.SmallJump.smallJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of one coordinate of the jump coefficient, restricted to the marks
  in `A m`.
* `LevyStochCalc.Ito.SmallJump.bigJumpProcess` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.SmallJump.measurable_uncurry_bigJumpProcess` — joint measurability of a
  coordinate of the big-jump process in the sample point and the time.
* `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` — `L²` convergence of
  the big-jump processes to the path at a fixed nonnegative time.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors along a subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors at almost every time of a bounded window, along a
  subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_comp` — the same, transported through a
  `C²` function of time and state.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_drift_bigJumpProcess`,
  `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_quadVar_bigJumpProcess` — pathwise
  convergence of the drift and quadratic-variation integrals along the big-jump processes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.SmallJump

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
variable {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable {Xp : ℝ → Ω → (Fin n → ℝ)} {A : ℕ → Set E}

section Basic

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

end Basic

section Limits

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

theorem _root_.LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => ∫⁻ ω,
        (‖bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by sorry
