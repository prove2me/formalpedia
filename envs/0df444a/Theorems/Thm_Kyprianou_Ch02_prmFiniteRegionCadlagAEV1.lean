-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
-- name    : Kyprianou.Ch02.prmFiniteRegionCadlagAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:56:00.738334+00:00
-- url     : https://prove2.me/theorems/f58b6102-786a-4d3a-a82a-e8e07dcceb88
-- title:
--   Almost-sure càdlàg paths of the finite-activity marked Poisson integral
-- statement:
--   Finite marks per bounded time interval imply a locally finite step-function representation, hence càdlàg paths on a common probability-one event.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8, finite-region Poisson integral; sound decomposition of the Chapter 2 theorem Kyprianou.finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47), itself already linked to Kyprianou.largeJumpProcessLevy (5c06d985-05f1-4c04-aa68-fc6de328bbfa).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionCadlagAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, IsCadlag (fun (t : ℝ≥0) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by sorry
