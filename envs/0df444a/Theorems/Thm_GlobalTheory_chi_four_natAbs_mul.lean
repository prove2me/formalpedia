-- Prove2me | Theorems.Thm_GlobalTheory_chi_four_natAbs_mul
-- name    : GlobalTheory.chi_four_natAbs_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:31.723352+00:00
-- url     : https://prove2.me/theorems/69e06e91-2866-43c5-9be0-09b7b6f0e902
-- title:
--   Global Theory: chi four nat Abs mul
-- statement:
--   The Global Theory construction uses the chi four nat Abs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L381-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L381-L386

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

theorem GlobalTheory.chi_four_natAbs_mul (D : ℤ) :
    ZMod.χ₄ (D.natAbs : ZMod 4) * D.natAbs = ZMod.χ₄ (D : ZMod 4) * D := by sorry
