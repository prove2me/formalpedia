-- Prove2me | Theorems.Thm_GlobalTheory_DCIndex_mem_sup_iff
-- name    : GlobalTheory.DCIndex.mem_sup_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:41.41741+00:00
-- url     : https://prove2.me/theorems/93642468-2ceb-4e9d-8ad7-be15ef72c68d
-- title:
--   DCIndex: mem sup iff
-- statement:
--   The DCIndex construction uses the mem sup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroup.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroup.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory GlobalTheory.DCIndex
variable {A : Type} [Group A]

theorem GlobalTheory.DCIndex.mem_sup_iff (hc : ∀ a b : A, a * b = b * a) (P Q : Subgroup A) {x : A} :
    x ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, p * q = x := by sorry
