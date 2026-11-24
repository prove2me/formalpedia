-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Chain_ofType_regular
-- name    : GlobalTheory.StepData.Chain.ofType_regular
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:19.940869+00:00
-- url     : https://prove2.me/theorems/ba52727e-0c8f-4312-88ee-015f4b570895
-- title:
--   Chain: of Type regular
-- statement:
--   The Chain construction uses the of Type regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L974-L978
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L974-L978

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
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.Chain.ofType_regular (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z) :
    (Chain.ofType P μ hμ F Ftop).Regular := by sorry
