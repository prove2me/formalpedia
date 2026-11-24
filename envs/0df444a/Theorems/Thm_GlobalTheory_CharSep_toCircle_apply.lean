-- Prove2me | Theorems.Thm_GlobalTheory_CharSep_toCircle_apply
-- name    : GlobalTheory.CharSep.toCircle_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:45.080855+00:00
-- url     : https://prove2.me/theorems/1afe0448-a40b-46e9-a6e4-afe762ce5355
-- title:
--   Char Sep: to Circle apply
-- statement:
--   The Char Sep construction uses the to Circle apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryAndSeparates.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryAndSeparates.lean#L42-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CharSep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CharSep.toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := by sorry
