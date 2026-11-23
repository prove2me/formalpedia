-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_ugFst_val
-- name    : GlobalTheory.WeilM.ugFst_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:38.299527+00:00
-- url     : https://prove2.me/theorems/a519d636-e50b-410f-9b6d-112dec0044c4
-- title:
--   Weil M: ug Fst val
-- statement:
--   The Weil M construction uses the ug Fst val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L160-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L160-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem GlobalTheory.WeilM.ugFst_val {J : Matrix β β (R × R)} (h : UG (swapA R) J) :
    (ugFst J h).val = cmp₁ ((h : GL β (R × R)) : Matrix β β (R × R)) := by sorry
