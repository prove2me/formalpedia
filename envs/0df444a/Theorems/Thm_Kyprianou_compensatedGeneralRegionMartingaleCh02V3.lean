-- Prove2me | Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3
-- name    : Kyprianou.compensatedGeneralRegionMartingaleCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:21:55.288243+00:00
-- url     : https://prove2.me/theorems/4ebdce06-f44e-471e-89e0-2d30a53b5aee
-- title:
--   Lemma 2.9: general finite-intensity compensated martingale
-- statement:
--   For every measurable B of finite Levy intensity and integrable jump sizes, the centred Poisson jump integral is a martingale relative to the completed natural filtration. Under the additional L2 moment condition it is square-integrable. The small-jump cutoff theorem already published is retained as a useful narrower consequence.
-- source:
--   Kyprianou (2006), Lemma 2.9(i)-(ii), pp. 45-46

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem compensatedGeneralRegionMartingaleCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B)) :
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
      MeasureTheory.Martingale
        (fun (t : ℝ≥0) ω =>
          (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
             z.2 ∂(N.N ω)) -
          (t : ℝ) * (∫ x in B, x ∂ν)) ℱ P ∧
      (MemLp (fun x : ℝ => x) 2 (ν.restrict B) →
       ∀ t : ℝ≥0, MemLp
         (fun ω =>
           (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              z.2 ∂(N.N ω)) -
           (t : ℝ) * (∫ x in B, x ∂ν)) 2 P)
    := by sorry

end Kyprianou
