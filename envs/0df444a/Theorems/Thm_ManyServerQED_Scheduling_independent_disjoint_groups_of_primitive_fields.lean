-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_independent_disjoint_groups_of_primitive_fields
-- name    : ManyServerQED.Scheduling.independent_disjoint_groups_of_primitive_fields
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:42:41.533633+00:00
-- url     : https://prove2.me/theorems/7b314584-5aaa-49ff-bebd-b4335c276ae9
-- title:
--   Independence of disjoint groups of independent fields
-- statement:
--   Given an independent family of sub-sigma-fields, the joins of pairwise disjoint groups of its fields form an independent family.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Set MeasureTheory ProbabilityTheory

theorem ManyServerQED.Scheduling.independent_disjoint_groups_of_primitive_fields {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : ι → MeasurableSpace Ω)
    (hLe : ∀ j, m j ≤ mΩ) (hInd : iIndep m P)
    (D : κ → Set ι) (hD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    iIndep (fun i => ⨆ j ∈ D i, m j) P := by sorry
