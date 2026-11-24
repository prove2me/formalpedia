-- Prove2me | Theorems.Thm_GlobalTheory_finite_quotient_range_mulVecLin
-- name    : GlobalTheory.finite_quotient_range_mulVecLin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:56.186289+00:00
-- url     : https://prove2.me/theorems/0eb3a72a-826d-4a41-b5d1-c34980f2a9b0
-- title:
--   Global Theory: finite quotient range mul Vec Lin
-- statement:
--   The Global Theory construction uses the finite quotient range mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L377-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L377-L379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}

theorem GlobalTheory.finite_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    Finite ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) := by sorry
