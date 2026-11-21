-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_contraction_real_core
-- name    : LevyStochCalc.BSDEJ.Solves.contraction_real_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:25:19.958004+00:00
-- url     : https://prove2.me/theorems/26880d81-58da-4c40-b0b1-b2e5c9a566db
-- title:
--   contraction real core
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.contraction_real_core` is extracted from `LevyStochCalc.BSDEJ.PicardContractionBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F000
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy and pointwise bounds behind the Picard contraction

The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm, the energy of a difference of two processes is finite when both energies are, and
freezing a process at the horizon leaves its energy there unchanged. At almost every time of the
horizon, twice the pairing of a process against the difference of two evaluations of a Lipschitz
generator is at most `β / 2` times the second moment of the process plus `6 L² / β` times the
sample energy density of the differenced arguments, and the real-variable core turns a weighted
energy dominated by such a pairing into a contraction by the factor `6 L² / β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

end Pointwise

section RealCore

theorem _root_.LevyStochCalc.BSDEJ.Solves.contraction_real_core {A Gout Gin V : ℝ → ℝ} {β c T : ℝ} (hβ : 2 ≤ β)
    (hA0 : ∀ s, 0 ≤ A s)
    (hAint : IntegrableOn (fun s => Real.exp (β * s) * A s) (Set.Icc (0 : ℝ) T))
    (hGoutint : IntegrableOn (fun s => Real.exp (β * s) * Gout s) (Set.Icc (0 : ℝ) T))
    (hGinint : IntegrableOn (fun s => Real.exp (β * s) * Gin s) (Set.Icc (0 : ℝ) T))
    (hVint : IntegrableOn (fun s => Real.exp (β * s) * V s) (Set.Icc (0 : ℝ) T))
    (hL : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s)
    (hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), V s ≤ β / 2 * A s + c * Gin s) :
    ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s
      ≤ c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by sorry
