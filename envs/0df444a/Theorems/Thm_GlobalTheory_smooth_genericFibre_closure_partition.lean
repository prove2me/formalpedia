-- Prove2me | Theorems.Thm_GlobalTheory_smooth_genericFibre_closure_partition
-- name    : GlobalTheory.smooth_genericFibre_closure_partition
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:26.170655+00:00
-- url     : https://prove2.me/theorems/6a916b43-c1e0-47be-9a5d-de61d68b741d
-- title:
--   Global Theory: smooth generic Fibre closure partition
-- statement:
--   The Global Theory construction uses the smooth generic Fibre closure partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothGenericFibreClosurePartition.lean#L9-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothGenericFibreClosurePartition.lean#L9-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartition
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
open GlobalTheory

theorem GlobalTheory.smooth_genericFibre_closure_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by sorry
