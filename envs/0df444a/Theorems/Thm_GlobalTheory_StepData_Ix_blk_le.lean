-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Ix_blk_le
-- name    : GlobalTheory.StepData.Ix.blk_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:31.935478+00:00
-- url     : https://prove2.me/theorems/1aa27ed9-6994-4130-8bed-145ab296ea07
-- title:
--   Ix: blk le
-- statement:
--   The Ix construction uses the blk le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L33-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.Ix.blk_le {j : ℕ} (a : Ix r t j) : a.blk ≤ j := by sorry
