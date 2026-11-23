-- Prove2me | Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty
-- name    : GlobalTheory.encard_smul_mem_le_encard_smul_inter_nonempty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:54.269428+00:00
-- url     : https://prove2.me/theorems/d04813fa-a684-45a8-ac3c-b24916a2f75c
-- title:
--   Global Theory: encard smul mem le encard smul inter nonempty
-- statement:
--   The Global Theory construction uses the encard smul mem le encard smul inter nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L14-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]

theorem GlobalTheory.encard_smul_mem_le_encard_smul_inter_nonempty (B : Set X) (x : X) :
    {g : G | g • x ∈ B}.encard ≤ {g : G | (g • B ∩ B).Nonempty}.encard := by sorry
