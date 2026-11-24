-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_extZ_add
-- name    : GlobalTheory.StepData.TypeDatum.extZ_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:55.811677+00:00
-- url     : https://prove2.me/theorems/462cf74c-f4be-4588-aabc-d03a6eee6901
-- title:
--   Type Datum: ext Z add
-- statement:
--   The Type Datum construction uses the ext Z add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L296-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L296-L304

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a)

theorem GlobalTheory.StepData.TypeDatum.extZ_add {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (M : Matrix a a k) {Y : Matrix a a k} (hY : MaxM Y) :
    extZ P.J (P.rho μ) (M + Y) = extZ P.J (P.rho μ) M := by sorry
