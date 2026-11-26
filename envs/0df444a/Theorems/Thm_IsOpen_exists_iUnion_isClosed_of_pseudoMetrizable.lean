-- Prove2me | Theorems.Thm_IsOpen_exists_iUnion_isClosed_of_pseudoMetrizable
-- name    : IsOpen.exists_iUnion_isClosed_of_pseudoMetrizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:51.715429+00:00
-- url     : https://prove2.me/theorems/66e57ef8-635a-488f-8c05-766efe4f8a41
-- title:
--   Is Open: exists i Union is Closed of pseudo Metrizable
-- statement:
--   In a (pseudo)metrizable space every open set is a countable union of
--       closed sets (complement of the Gδ representation of its complement;
--       Mathlib's `IsOpen.exists_iUnion_isClosed` is the pseudo-emetric
--       version — this one works directly at the topology level).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L167-L185
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L167-L185

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]

theorem IsOpen.exists_iUnion_isClosed_of_pseudoMetrizable
    {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {U : Set X} (hU : IsOpen U) :
    ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ U = ⋃ n, C n := by sorry
