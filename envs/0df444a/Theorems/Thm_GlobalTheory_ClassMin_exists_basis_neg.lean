-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_exists_basis_neg
-- name    : GlobalTheory.ClassMin.exists_basis_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:17.426949+00:00
-- url     : https://prove2.me/theorems/bf2ed378-19c7-4777-8f33-ce9a87929578
-- title:
--   Class Min: exists basis neg
-- statement:
--   The Class Min construction uses the exists basis neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L53-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
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
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}

theorem GlobalTheory.ClassMin.exists_basis_neg {ι : Type*} (e : Basis ι ℤ X) {ν : X →+ ℝ} (hν : ν ≠ 0) :
    ∃ i, ν (e i) < 0 ∨ ν (-e i) < 0 := by sorry
