-- Prove2me | Theorems.Thm_GlobalTheory_StepData_HasTypes_transport
-- name    : GlobalTheory.StepData.HasTypes.transport
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:34.452811+00:00
-- url     : https://prove2.me/theorems/c831a801-317e-4a45-bf1d-9d9a7fd87858
-- title:
--   Has Types: transport
-- statement:
--   The Has Types construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1139-L1149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1139-L1149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.HasTypes.transport {Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {μ : kˣ →* ℂˣ}
    {P' : Level (GL a k)} {P : Level (GL b k)} {Φ : Matrix b a k → ℂ} (H : HasTypes μ P' P Φ)
    (F : LatFrame k b Y) (F' : LatFrame k a Y') :
    HasTypes μ (P'.map F'.conj) (P.map F.conj) (F.transport F' Φ) := by sorry
