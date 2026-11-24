-- Prove2me | Theorems.Thm_GlobalTheory_frobSemilinear_iterate_eq_zero
-- name    : GlobalTheory.frobSemilinear_iterate_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:11.639509+00:00
-- url     : https://prove2.me/theorems/184f4c0c-c5ab-4107-821d-dfff68accbc4
-- title:
--   Global Theory: frob Semilinear iterate eq zero
-- statement:
--   The Global Theory construction uses the frob Semilinear iterate eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten.lean#L7-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten.lean#L7-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.frobSemilinear_iterate_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by sorry
