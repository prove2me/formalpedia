-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_stopped_sub_cells
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T07:53:28.670331+00:00
-- url     : https://prove2.me/theorems/6e4b0273-2d71-4af0-a76f-92356c64bd7a
-- title:
--   stochasticIntegralBrownian stopped sub cells
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` is extracted from `LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a simple random vector

On a cell where a stopping time and a simple random mark are both constant the translation is by
a fixed vector, so the cell indicator — bounded and known at the deterministic time carried by
the cell — passes inside the Itô integral of the increment, and the Itô integral of the increment
read along the mark splits over the cells. Itô's formula for the increment between the two
stopping times then applies on each cell with a constant shift, and recombining the cells gives
the formula for a function translated by the simple random vector. The cells themselves are
measurable at the deterministic times the stopping time takes as soon as the mark is measurable
at that stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` — the Itô integral of
  that increment splits over the cells.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_simpleShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a simple random vector.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_of_measurable` — a mark measurable at a stopping
  time has cells measurable at the deterministic times that stopping time takes.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*}
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {c : Ω → α} {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs)
    {J : Finset ℝ} {T : ℝ} (hJ0 : ∀ a ∈ J, 0 ≤ a) (hJT : ∀ a ∈ J, a < T)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hmK : ∀ v, Measurable (Function.uncurry (K v)))
    (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    (hqK : ∀ (v : α) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s)
    (hmc : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s))
    (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
    (hqc : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hT : 0 < T) :
    ∀ᵐ ω ∂P, stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
        hmc hpc hqc T ω
      = ∑ x ∈ J ×ˢ Vs, cellWeight σ c x.1 x.2 ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)
          (measurable_uncurry_stopped_sub hσ hτ (hmK x.2))
          (progressivelyMeasurable_stopped_sub hσ hτ (hpK x.2))
          (energy_stopped_sub_lt_top hσ hτ (hmK x.2) (hqK x.2)) T ω := by sorry
