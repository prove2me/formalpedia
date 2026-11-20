-- Prove2me | Theorems.Thm_LevyStochCalc_Martingale_exists_adapted_ae_cadlag
-- name    : LevyStochCalc.Martingale.exists_adapted_ae_cadlag
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:37:26.456568+00:00
-- url     : https://prove2.me/theorems/19e78964-a00f-4422-a9af-861e78a2038a
-- title:
--   exists adapted ae cadlag
-- statement:
--   The source theorem `LevyStochCalc.Martingale.exists_adapted_ae_cadlag` is extracted from `LevyStochCalc.Martingale.CadlagModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of real martingales

A real martingale on a right-continuous filtration whose time slices are right-continuous
in measure admits an adapted modification whose paths are almost surely càdlàg. The
modification is the right-limit regularisation along a countable dense set of times
(`ProbabilityTheory.rightContModif`), available for real quasimartingales; a martingale is
a quasimartingale because the elementary integral of a predictable indicator against it has
zero mean.

Two index sets are treated: `ℝ≥0`, where the quasimartingale theory lives (it needs a least
time), and `ℝ`, by restricting to nonnegative times and extending by zero to negative times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Martingale

section Modification

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} {X Y : ι → Ω → ℝ}

end Modification

section Quasimartingale

variable {ι Ω : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ι mΩ} {μ : Measure Ω} {X : ι → Ω → ℝ}

variable [OrderBot ι]

end Quasimartingale

section NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

end NNReal

section Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}

theorem _root_.LevyStochCalc.Martingale.exists_adapted_ae_cadlag [ℱ.IsRightContinuous] (hX : Martingale X ℱ μ)
    (hrc : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t))
    (hneg : ∀ t, t < 0 → X t =ᵐ[μ] 0) :
    ∃ Y : ℝ → Ω → ℝ, Adapted ℱ Y ∧ (∀ t, Y t =ᵐ[μ] X t) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by sorry
