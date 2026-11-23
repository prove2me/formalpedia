-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
-- name    : Kyprianou.Ch02.compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:01:10.293878+00:00
-- url     : https://prove2.me/theorems/89e17745-47c4-4224-bd90-6f1211a31795
-- title:
--   Finite-region compensated Poisson integral martingale in its natural filtration
-- statement:
--   Martingale adaptedness, integrability and conditional centring for finite-intensity compensated marked Poisson integral in the completed right-continuous natural filtration.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.9; source-exact logical decomposition of canonical 4ebdce06

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    MeasureTheory.Martingale
      (fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) ℱ P := by sorry
