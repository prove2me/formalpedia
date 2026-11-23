-- Prove2me | Theorems.Thm_GlobalTheory_StepData_inv_mul_mem_KOne
-- name    : GlobalTheory.StepData.inv_mul_mem_KOne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:17.953681+00:00
-- url     : https://prove2.me/theorems/2e020d9b-dac1-4f36-8f40-81544e80b9e2
-- title:
--   Step Data: inv mul mem KOne
-- statement:
--   The Step Data construction uses the inv mul mem KOne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L138-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
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
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.StepData.inv_mul_mem_KOne {g g' : GL n k} (hg : g ∈ KO k n) (h : MaxM (g'.val - g.val)) : g⁻¹ * g' ∈ KOne k n := by sorry
