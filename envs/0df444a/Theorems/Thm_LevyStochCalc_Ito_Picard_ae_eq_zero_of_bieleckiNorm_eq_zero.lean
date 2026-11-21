-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_eq_zero_of_bieleckiNorm_eq_zero
-- name    : LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:50:08.87518+00:00
-- url     : https://prove2.me/theorems/d0291cfe-a10a-444b-9ade-fed981596888
-- title:
--   ae eq zero of bieleckiNorm eq zero
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero` is extracted from `LevyStochCalc.Ito.PicardContractionFixedPoint`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The fixed point of the Picard step

The limit `picardLimit` of the Picard iterates is jointly measurable, progressively measurable and
of finite Bielecki norm, and the Bielecki distance between the step taken along it and the limit
itself vanishes, so the step and the limit agree almost surely at every time of the window. The
step contracts between two raw state processes and therefore respects almost sure equality of its
input, which promotes that agreement to the statement that the process built over the limit solves
the Picard equation along its own path.

## Main statements

* `picardLimit` — the limit of the Picard iterates.
* `bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero` — the limit is a fixed point in norm.
* `picardSelfMapRaw_picardLimit_ae_eq` — the fixed point is realised by a process of the space.
* `picardSelfMapRaw_isFixedPoint` — the fixed point solves its own Picard equation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The fixed point -/

variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in

theorem _root_.LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero {β T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZs : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => Z u ω i)
    (h : bieleckiNorm (P := P) β T Z = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0 := by sorry
