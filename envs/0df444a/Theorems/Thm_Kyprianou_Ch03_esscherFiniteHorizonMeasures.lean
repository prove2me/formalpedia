-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherFiniteHorizonMeasures
-- name    : Kyprianou.Ch03.esscherFiniteHorizonMeasures
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:47:29.010745+00:00
-- url     : https://prove2.me/theorems/4de18e7b-b85e-4852-ab04-e21c798624d2
-- title:
--   Esscher measures: finite-horizon probability laws and restriction consistency
-- statement:
--   Finite-horizon Esscher measures are probabilities and restrict consistently. A global extension requires a suitable measurable-space extension theorem, not silently assumed.
-- source:
--   Kyprianou (2006), printed pp. 78-80; finite-horizon construction.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherFiniteHorizonMeasures
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (beta k : ℝ)
    (hDensity : ∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1)
    (hConsistent : ∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) :
    (∀ t : NNReal,
      P.withDensity (fun omega =>
        ENNReal.ofReal (esscherDensity X beta k t omega)) Set.univ = 1) ∧
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k s omega))) A =
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k t omega))) A) := by
  sorry

end Kyprianou.Ch03
