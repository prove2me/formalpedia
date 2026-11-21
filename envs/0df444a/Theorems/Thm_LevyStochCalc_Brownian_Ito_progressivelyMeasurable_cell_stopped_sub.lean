-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_progressivelyMeasurable_cell_stopped_sub
-- name    : LevyStochCalc.Brownian.Ito.progressivelyMeasurable_cell_stopped_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:44:18.810648+00:00
-- url     : https://prove2.me/theorems/3669b99d-61ee-48b0-bdb7-d708b396758c
-- title:
--   progressivelyMeasurable cell stopped sub
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_cell_stopped_sub` is extracted from `LevyStochCalc.Ito.ItoFormulaSimpleShiftCells`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cells of a stopping time and a simple random mark

A random mark taking finitely many values, together with a stopping time taking finitely many
deterministic values below a horizon, decomposes the sample space into the cells on which both
are constant. The indicator of such a cell is bounded by one and, when the cell is known at the
deterministic time the stopping time takes there, it is measurable at that time; summing the
indicators against a function of the mark recovers that function read along the mark.
Consequently the increment of an integrand read along the mark between two stopping times is the
finite sum of the cell integrands, each of which is a bounded weight vanishing before the
deterministic time of its cell times an increment vanishing up to that time, hence progressively
measurable with finite energy on bounded windows.

## Main statements

* `LevyStochCalc.Brownian.Ito.cellWeight` — the indicator of a cell of the decomposition.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_weight_mul_stopped_sub` — a bounded weight
  known at a deterministic time, times an increment vanishing up to that time, is progressively
  measurable.
* `LevyStochCalc.Brownian.Ito.stopped_sub_eq_sum_cells` — the increment of an integrand read
  along a simple random mark is the sum of its cell integrands.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_simple` — that increment is
  progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellWeight

variable {Ω : Type u} {α : Type*}

variable (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeight

section CellWeightMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeightMeasurable

section CellWeightSum

variable {Ω : Type u} {α : Type*} (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeightSum

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

end Weight

section WeightEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

end WeightEnergy

section CellFamily

variable {Ω : Type u} {α : Type*} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

end CellFamily

section CellFamilyProgressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

theorem _root_.LevyStochCalc.Brownian.Ito.progressivelyMeasurable_cell_stopped_sub
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) (hcVs : ∀ ω, c ω ∈ Vs) (hJ0 : ∀ a ∈ J, 0 ≤ a)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    (x : ℝ × α) :
    Probability.ProgressivelyMeasurable ℱ
      (fun (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)) := by sorry
