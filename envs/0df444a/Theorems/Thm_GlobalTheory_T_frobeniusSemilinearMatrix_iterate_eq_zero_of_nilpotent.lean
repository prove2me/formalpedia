-- Prove2me | Theorems.Thm_GlobalTheory_T_frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent
-- name    : GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:21.487019+00:00
-- url     : https://prove2.me/theorems/999f5f9d-8fa0-5a1f-a211-6952b93dc26c
-- title:
--   T: frobenius Semilinear Matrix iterate eq zero of nilpotent
-- statement:
--   The T construction uses the frobenius Semilinear Matrix iterate eq zero of nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusSemilinearMatrixIterateEqZeroOfNilpotenStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusSemilinearMatrixIterateEqZeroOfNilpotenStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSemilinearMatrixIterateEqZeroOfNilpotenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by sorry
