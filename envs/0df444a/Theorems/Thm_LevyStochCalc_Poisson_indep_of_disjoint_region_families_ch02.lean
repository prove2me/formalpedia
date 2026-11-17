-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_indep_of_disjoint_region_families_ch02
-- name    : LevyStochCalc.Poisson.indep_of_disjoint_region_families_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T00:03:18.197504+00:00
-- url     : https://prove2.me/theorems/9849fbff-c30c-4370-bbf5-9dc3fee263b9
-- title:
--   Chapter 2 region-independence chain: indep_of_disjoint_region_families
-- statement:
--   Original source theorem of finite-partition/Poisson-evaluation independence, with the original quantifiers and hypotheses; proof obligations are unchanged.
-- source:
--   LevyStochCalc/Poisson/RegionIndependence.lean, Apache-2.0

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

universe u v
namespace LevyStochCalc.Poisson
variable {Ω : Type u} [MeasurableSpace Ω]
  {𝓨 : Type v} [MeasurableSpace 𝓨]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {N : Ω → Measure 𝓨}
theorem indep_of_disjoint_region_families_ch02
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {p : ℕ} (D : Fin p → Set 𝓨) (hD : ∀ j, MeasurableSet (D j)) :
    Indep (⨆ C ∈ {C : Set 𝓨 | (∀ j, Disjoint C (D j)) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N ω C) inferInstance)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by sorry
end LevyStochCalc.Poisson
