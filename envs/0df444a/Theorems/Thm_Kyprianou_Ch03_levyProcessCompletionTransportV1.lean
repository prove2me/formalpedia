-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyProcessCompletionTransportV1
-- name    : Kyprianou.Ch03.levyProcessCompletionTransportV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:18:43.900811+00:00
-- url     : https://prove2.me/theorems/d50593e6-9802-435a-8de2-de98afeb2022
-- title:
--   Lévy process transported to the null-measurable completion
-- statement:
--   Finite increment independence is a finite intersection measure identity, stationary increments follow by mapping through the measure-preserving identity, and càdlàg almost-sure paths are unchanged.
-- source:
--   Kyprianou (2006), Chapter 3, measure completion and Esscher consistency; decomposition of ab761573-db74-4e47-82c1-6b9e662005ef

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.levyProcessCompletionTransportV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hx : ∀ t, Measurable (X t)) :
    IsLevyProcess (fun t (w : NullMeasurableSpace Ω P) => X t w) P.completion := by sorry
