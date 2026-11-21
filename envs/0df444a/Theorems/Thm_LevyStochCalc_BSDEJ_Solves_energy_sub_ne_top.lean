-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_energy_sub_ne_top
-- name    : LevyStochCalc.BSDEJ.Solves.energy_sub_ne_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:31:55.49712+00:00
-- url     : https://prove2.me/theorems/cf0da9ef-d9e9-4a78-ba1f-fcd709a789a8
-- title:
--   energy sub ne top
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.energy_sub_ne_top` is extracted from `LevyStochCalc.BSDEJ.PicardContractionBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.BSDEJ.Solves.energy_sub_ne_top {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (h₁ : Brownian.Ito.energy P T H₁ ≠ ⊤)
    (h₂ : Brownian.Ito.energy P T H₂ ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) ≠ ⊤ := by sorry
