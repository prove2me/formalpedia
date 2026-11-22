-- Prove2me | Theorems.Thm_Measurable_measurableSet_edist_eqOn_zero_of_continuous
-- name    : Measurable.measurableSet_edist_eqOn_zero_of_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:42:43.20261+00:00
-- url     : https://prove2.me/theorems/0202f7ed-011b-4c3f-9529-375af0550fbc
-- title:
--   measurableSet edist eqOn zero of continuous
-- statement:
--   The source theorem `Measurable.measurableSet_edist_eqOn_zero_of_continuous` is extracted from `BrownianMotion.Continuity.KolmogorovChentsov`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

theorem _root_.Measurable.measurableSet_edist_eqOn_zero_of_continuous [SecondCountableTopology T]
    {f g : T → Ω → E} (hU : IsOpen U)
    (hf : ∀ ω, ContinuousOn (f · ω) U) (hg : ∀ ω, ContinuousOn (g · ω) U)
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t ∈ U, edist (f t ω) (g t ω) = 0} := by sorry
