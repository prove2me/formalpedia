-- Prove2me | Theorems.Thm_GlobalTheory_pow_sub_pow_mem_pow_succ
-- name    : GlobalTheory.pow_sub_pow_mem_pow_succ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:54.391874+00:00
-- url     : https://prove2.me/theorems/b0972703-e691-49fd-bc54-2bb4a45897dc
-- title:
--   Global Theory: pow sub pow mem pow succ
-- statement:
--   The Global Theory construction uses the pow sub pow mem pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L289-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L289-L299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.pow_sub_pow_mem_pow_succ {R : Type*} [CommRing R] {I : Ideal R} {a b : R} (ha : a ∈ I)
    (hb : b ∈ I) (hab : a - b ∈ I ^ 2) (d : ℕ) : a ^ d - b ^ d ∈ I ^ (d + 1) := by sorry
