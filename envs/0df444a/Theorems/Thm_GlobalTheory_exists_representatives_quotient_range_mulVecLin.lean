-- Prove2me | Theorems.Thm_GlobalTheory_exists_representatives_quotient_range_mulVecLin
-- name    : GlobalTheory.exists_representatives_quotient_range_mulVecLin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:22.231805+00:00
-- url     : https://prove2.me/theorems/687585be-ecbb-4696-99e5-31cf20ceb3a4
-- title:
--   Global Theory: exists representatives quotient range mul Vec Lin
-- statement:
--   The Global Theory construction uses the exists representatives quotient range mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L436-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L436-L443

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

theorem GlobalTheory.exists_representatives_quotient_range_mulVecLin (hd : d.det ≠ 0) :
    ∃ r : Fin d.det.natAbs → n → ℤ, Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin) := by sorry
