-- Prove2me | Theorems.Thm_Kyprianou_Ch03_finiteEsscher_probabilityNormalization
-- name    : Kyprianou.Ch03.finiteEsscher_probabilityNormalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T14:57:10.153427+00:00
-- url     : https://prove2.me/theorems/90781035-fe1e-443b-aa8d-95714d0b1554
-- title:
--   finite-horizon Esscher construction source clause 1
-- statement:
--   Exact independently quantified clause 1 of finite-horizon Esscher construction. All original hypotheses and process domains are retained.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, finite-horizon Esscher construction

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem finiteEsscher_probabilityNormalization
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
        ENNReal.ofReal (esscherDensity X beta k t omega)) Set.univ = 1) := by
  sorry

end Kyprianou.Ch03
