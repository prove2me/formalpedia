-- Prove2me | Theorems.Thm_GlobalTheory_StepData_parPhi_mul_left
-- name    : GlobalTheory.StepData.parPhi_mul_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:47.052214+00:00
-- url     : https://prove2.me/theorems/0fa7787a-70bb-418d-8728-1e0f08b79ba8
-- title:
--   Step Data: par Phi mul left
-- statement:
--   The Step Data construction uses the par Phi mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1101-L1122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1101-L1122

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
omit [Fintype s'] [DecidableEq s']

theorem GlobalTheory.StepData.parPhi_mul_left (hδ : IsTame δ) (g : (TypeDatum.full k r).stepJ s) (x : Matrix (r ⊕ s) (r ⊕ s') k) :
    parPhi δ ((g : GL (r ⊕ s) k).val * x) =
      (TypeDatum.full k r).rho δ ((TypeDatum.full k r).corner g) * parPhi δ x := by sorry
