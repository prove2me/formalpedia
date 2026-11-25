-- Prove2me | Theorems.Thm_GlobalTheory_T_closure_generic_fibre_clopen_split_alt
-- name    : GlobalTheory.T.closure_generic_fibre_clopen_split_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:11.845802+00:00
-- url     : https://prove2.me/theorems/f610df97-c6a5-453c-9e05-c79d53d71632
-- title:
--   T: closure generic fibre clopen split alt
-- statement:
--   The T construction uses the closure generic fibre clopen split alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosureGenericFibreClopenSplitStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosureGenericFibreClopenSplitStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplitStatement
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

theorem GlobalTheory.T.closure_generic_fibre_clopen_split_alt : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by sorry
