-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stronglyMeasurable_clip
-- name    : LevyStochCalc.Brownian.Ito.stronglyMeasurable_clip
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:46:59.490782+00:00
-- url     : https://prove2.me/theorems/42f88c5d-65b3-4371-b7be-f9cb4c966f39
-- title:
--   stronglyMeasurable clip
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stronglyMeasurable_clip` is extracted from `LevyStochCalc.Brownian.VectorItoStopped`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.stronglyMeasurable_clip {X : ℝ → Ω → Fin n → ℝ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hX : ∀ r : ℝ, @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ r) (X r))
    (J : Finset ℝ)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤)
    (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ t)
      (fun ω => X (clipTime τ t ω) ω) := by sorry
