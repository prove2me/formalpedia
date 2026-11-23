-- Prove2me | Theorems.Thm_GlobalTheory_natCard_quotient_range_mulVecLin
-- name    : GlobalTheory.natCard_quotient_range_mulVecLin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:50.480796+00:00
-- url     : https://prove2.me/theorems/c4f34a68-78d7-44fe-a66f-ff8385fb2262
-- title:
--   Global Theory: nat Card quotient range mul Vec Lin
-- statement:
--   The Global Theory construction uses the nat Card quotient range mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L369-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L369-L375

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

theorem GlobalTheory.natCard_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    Nat.card ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) = d.det.natAbs := by sorry
