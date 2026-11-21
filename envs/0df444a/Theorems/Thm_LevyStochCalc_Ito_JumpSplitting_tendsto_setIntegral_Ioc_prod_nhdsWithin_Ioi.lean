-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi
-- name    : LevyStochCalc.Ito.JumpSplitting.tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:52:20.632905+00:00
-- url     : https://prove2.me/theorems/1c38bce8-8ec2-4dcb-9515-ddae724a23a5
-- title:
--   tendsto setIntegral Ioc prod nhdsWithin Ioi
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi` is extracted from `LevyStochCalc.Ito.JumpSplittingLeftLim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000
import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting along the left limits of the path

The jump coefficient of a jump diffusion can be evaluated along the left limits of the path
instead of along the path itself. The two integrands agree off a countable set of times, so they
have the same compensated integral, while the pathwise integral against the random measure and
the compensator against the reference intensity are both taken with the left-limit integrand.
The drift carrying the compensator of the left-limit integrand agrees with the drift carrying
that of the path integrand at almost every time of every horizon, so the two build the same
vector Itô process.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.leftLimPath` — the left limits of the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeft` — the pathwise sum of the jumps carried by a mark
  set over a time window, with the jump coefficient evaluated at the left limits of the path.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeft` — the drift of a jump diffusion with the
  compensator of the left-limit jump coefficient subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSumLeft_nhdsWithin_Ioi` — the left-limit jump sum
  over `(0, ·]` is right-continuous in time.
* `LevyStochCalc.Ito.JumpSplitting.ae_ae_restrict_continuousDriftLeft_eq` and
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_vectorItoProcess_continuousDriftLeft_eq` — the two
  drifts agree at almost every time of every horizon, hence build the same vector Itô process.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section WindowContinuity

variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Ito.JumpSplitting.tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi {κ : Measure (ℝ × E)} {A : Set E}
    (hA : MeasurableSet A) {f : ℝ × E → ℝ} (hf : Measurable f)
    (hint : ∀ T : ℝ, IntegrableOn f (Set.Ioc (0 : ℝ) T ×ˢ A) κ) (t : ℝ) :
    Tendsto (fun s => ∫ q in Set.Ioc (0 : ℝ) s ×ˢ A, f q ∂κ) (𝓝[>] t)
      (𝓝 (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, f q ∂κ)) := by sorry
