-- Prove2me | Theorems.Thm_GlobalTheory_CharSep_norm_le_one
-- name    : GlobalTheory.CharSep.norm_le_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:09.462017+00:00
-- url     : https://prove2.me/theorems/3c3395ad-450d-4e4d-bde9-8c5fe250dea7
-- title:
--   Char Sep: norm le one
-- statement:
--   The Char Sep construction uses the norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryAndSeparates.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryAndSeparates.lean#L12-L23

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

theorem GlobalTheory.CharSep.norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by sorry
