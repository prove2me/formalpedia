-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyNonanticipatingFiltrationV1
-- name    : Kyprianou.Ch05.pointFamilyNonanticipatingFiltrationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:46:46.828078+00:00
-- url     : https://prove2.me/theorems/3753eef8-b93f-47c1-9e93-5dc00b847ec5
-- title:
--   Canonical non-negative-time Poisson measure has a nonanticipating filtration
-- statement:
--   The finite evaluation sigma-algebras define an increasing filtration. Disjoint-region independence and the arbitrary-region evaluation lemma give the future count independence required by Chapter 4.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.pointFamilyNonanticipatingFiltrationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P Pi)
    (hN : ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ)) :
    ∃ F : Filtration NNReal inferInstance,
      Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P Pi F N ∧
      ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi) (Iic (t : ℝ) ×ˢ univ) := by
  sorry
