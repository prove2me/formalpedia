-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_indep_iSup_comap_of_disjoint_families_ch02
-- name    : LevyStochCalc.Poisson.indep_iSup_comap_of_disjoint_families_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T00:03:18.032969+00:00
-- url     : https://prove2.me/theorems/417229e0-4370-4a5c-be3c-fa4cc01c5063
-- title:
--   Chapter 2 region-independence chain: indep_iSup_comap_of_disjoint_families
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
theorem indep_iSup_comap_of_disjoint_families_ch02
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {n p : ℕ} (C : Fin n → Set 𝓨) (D : Fin p → Set 𝓨)
    (hC : ∀ i, MeasurableSet (C i)) (hD : ∀ j, MeasurableSet (D j))
    (hCD : ∀ i j, Disjoint (C i) (D j)) :
    Indep (⨆ i, MeasurableSpace.comap (fun ω => N ω (C i)) inferInstance)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by sorry
end LevyStochCalc.Poisson
