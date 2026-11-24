-- Prove2me | Theorems.Thm_GlobalTheory_StepData_parPhi_mul_right
-- name    : GlobalTheory.StepData.parPhi_mul_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:11.437451+00:00
-- url     : https://prove2.me/theorems/f6bd3688-cdfa-4ac7-a984-d40131a508b9
-- title:
--   Step Data: par Phi mul right
-- statement:
--   The Step Data construction uses the par Phi mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1077-L1098
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1077-L1098

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
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s']
  {δ : kˣ →* ℂˣ}
omit [Fintype s] [DecidableEq s]

theorem GlobalTheory.StepData.parPhi_mul_right (hδ : IsTame δ) (g : (TypeDatum.full k r).stepJ s') (x : Matrix (r ⊕ s) (r ⊕ s') k) :
    parPhi δ (x * (g : GL (r ⊕ s') k).val) =
      (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g) * parPhi δ x := by sorry
