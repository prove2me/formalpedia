-- Prove2me | Theorems.Thm_GlobalTheory_CharFlag_subRep_apply
-- name    : GlobalTheory.CharFlag.subRep_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:03:00.504196+00:00
-- url     : https://prove2.me/theorems/6249d1dd-ceee-4d79-8436-d4e9b972408b
-- title:
--   Char Flag: sub Rep apply
-- statement:
--   The Char Flag construction uses the sub Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubRepApply.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubRepApply.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CharFlag
variable {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]

theorem GlobalTheory.CharFlag.subRep_apply (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) (g : Γ) (x : S) :
    ((subRep π S hS g x : S) : V) = π g x := by sorry
