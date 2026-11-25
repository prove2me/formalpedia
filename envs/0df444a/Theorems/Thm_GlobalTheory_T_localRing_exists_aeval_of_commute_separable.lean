-- Prove2me | Theorems.Thm_GlobalTheory_T_localRing_exists_aeval_of_commute_separable
-- name    : GlobalTheory.T.localRing_exists_aeval_of_commute_separable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:18.838649+00:00
-- url     : https://prove2.me/theorems/ac260380-c9b3-574c-bf2d-d1c926c60f16
-- title:
--   T: local Ring exists aeval of commute separable
-- statement:
--   The T construction uses the local Ring exists aeval of commute separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalRingExistsAevalOfCommuteSeparableStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalRingExistsAevalOfCommuteSeparableStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingExistsAevalOfCommuteSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingExistsAevalOfCommuteSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.localRing_exists_aeval_of_commute_separable : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y T : Matrix (Fin n) (Fin n) R), Y.charpoly.Separable → T * Y = Y * T → ∃ p : R[X], T = aeval Y p := by sorry
