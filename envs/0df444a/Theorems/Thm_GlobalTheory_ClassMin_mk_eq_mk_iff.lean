-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_mk_eq_mk_iff
-- name    : GlobalTheory.ClassMin.mk_eq_mk_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:15.645975+00:00
-- url     : https://prove2.me/theorems/eeffd07c-4499-4325-9e4a-47ab38c98675
-- title:
--   Class Min: mk eq mk iff
-- statement:
--   The Class Min construction uses the mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L16-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
import Theorems.Thm_GlobalTheory_IsSiegel_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]

theorem GlobalTheory.ClassMin.mk_eq_mk_iff (N : ℤ) (a b : X) :
    (Submodule.Quotient.mk b : QuotSMulTop N X) = Submodule.Quotient.mk a ↔ ∃ w, b = a + N • w := by sorry
