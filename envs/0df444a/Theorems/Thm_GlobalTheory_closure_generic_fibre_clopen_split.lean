-- Prove2me | Theorems.Thm_GlobalTheory_closure_generic_fibre_clopen_split
-- name    : GlobalTheory.closure_generic_fibre_clopen_split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:33.418143+00:00
-- url     : https://prove2.me/theorems/c46a4c42-0670-4fc1-a143-de5975b4a0f7
-- title:
--   Global Theory: closure generic fibre clopen split
-- statement:
--   The Global Theory construction uses the closure generic fibre clopen split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosureGenericFibreClopenSplit.lean#L7-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosureGenericFibreClopenSplit.lean#L7-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplit
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

theorem GlobalTheory.closure_generic_fibre_clopen_split : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by sorry
