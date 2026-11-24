-- Prove2me | Theorems.Thm_GlobalTheory_StepData_blk_ixSucc_inr
-- name    : GlobalTheory.StepData.blk_ixSucc_inr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:26.833062+00:00
-- url     : https://prove2.me/theorems/559a7c76-961e-421d-babc-62b39801c0cc
-- title:
--   Step Data: blk ix Succ inr
-- statement:
--   The Step Data construction uses the blk ix Succ inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L30-L30

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

theorem GlobalTheory.StepData.blk_ixSucc_inr {j : ℕ} (s : t) : (ixSucc r t j (.inr s)).blk = j + 1 := by sorry
