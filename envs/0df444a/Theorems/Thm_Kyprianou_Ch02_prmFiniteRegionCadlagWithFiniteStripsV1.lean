-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagWithFiniteStripsV1
-- name    : Kyprianou.Ch02.prmFiniteRegionCadlagWithFiniteStripsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:20:39.681802+00:00
-- url     : https://prove2.me/theorems/354507ab-700a-49c4-9dc1-ffa67e5faf0a
-- title:
--   Càdlàg finite-region Poisson integral assuming common almost-sure finite unit-strip counts
-- statement:
--   For an arbitrary Poisson random measure satisfying the exact LevyStochCalc structure, finite-rate mark region, and one full-probability event of finite atom counts on each unit time strip, derive almost-sure cadlag paths of the cumulative marked integral. The substantial remaining argument is simultaneous atomicity and a finite-step path representation, using countable generation of real Borel subsets. This theorem is a genuine sufficient condition for the Chapter 2 finite-region integral cadlag obligation.
-- source:
--   Kyprianou (2006), Ch. 2, Lemma 2.8. Reduction of Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 (f58b6102-786a-4d3a-a82a-e8e07dcceb88); uses proved Kyprianou.Ch02.prmUnitStripsFiniteMassAEV1 (a2a031b3-f58b-405b-a592-0ead322706f5), itself connected to Chapter 2 Eq. (2.3).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionCadlagWithFiniteStripsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hCount : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ico (n : ℝ) (n + 1) ×ˢ B) = k) :
    ∀ᵐ ω ∂P, IsCadlag (fun (t : ℝ≥0) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by sorry
