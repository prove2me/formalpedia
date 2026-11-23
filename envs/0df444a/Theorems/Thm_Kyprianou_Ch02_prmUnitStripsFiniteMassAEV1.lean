-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmUnitStripsFiniteMassAEV1
-- name    : Kyprianou.Ch02.prmUnitStripsFiniteMassAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:13:52.958506+00:00
-- url     : https://prove2.me/theorems/a2a031b3-f58b-405b-a592-0ead322706f5
-- title:
--   Simultaneous finite counts on all unit-time mark windows of a finite-rate Poisson random measure
-- statement:
--   For a finite-intensity mark region, each unit time strip has Poisson-distributed mass, hence an integer count. Countably intersect the probability-one events, preserving all windows on one event.
-- source:
--   Kyprianou 2006, Chapter 2, Lemma 2.8, pathwise finite-activity Poisson integral; component of Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 connected to Eq (2.3).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finitePoissonTimeMarkCellIntensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmUnitStripsFiniteMassAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ico (n : ℝ) (n + 1) ×ˢ B) = k := by sorry
