-- Prove2me | Theorems.Thm_GlobalTheory_T_disjoint_closure_and_union_eq_univ_of_genericFibre_partition
-- name    : GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:25.763316+00:00
-- url     : https://prove2.me/theorems/1fa3e52e-213c-48f3-8644-5f0a5123dd02
-- title:
--   T: disjoint closure and union eq univ of generic Fibre partition
-- statement:
--   The T construction uses the disjoint closure and union eq univ of generic Fibre partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothGenericFibreClosurePartitionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothGenericFibreClosurePartitionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartitionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by sorry
