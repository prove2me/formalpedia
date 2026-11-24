-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_hasTypes_iterPhi
-- name    : GlobalTheory.StepData.TypeDatum.hasTypes_iterPhi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:07.340463+00:00
-- url     : https://prove2.me/theorems/597d575e-6505-4f11-8e68-0d3ee4010815
-- title:
--   Type Datum: has Types iter Phi
-- statement:
--   The Type Datum construction uses the has Types iter Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1151-L1169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1151-L1169

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

theorem GlobalTheory.StepData.TypeDatum.hasTypes_iterPhi {r : Type*} [Fintype r] [DecidableEq r] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    HasTypes (μ (j + 1)) (P.iter t μ hμ j).toLevel (P.iter t μ hμ (j + 1)).toLevel (P.iterPhi t μ hμ j) := by sorry
