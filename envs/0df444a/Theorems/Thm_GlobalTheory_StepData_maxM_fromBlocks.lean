-- Prove2me | Theorems.Thm_GlobalTheory_StepData_maxM_fromBlocks
-- name    : GlobalTheory.StepData.maxM_fromBlocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:29.569568+00:00
-- url     : https://prove2.me/theorems/22ef76ee-70ac-4b16-a9a9-7da4e305b38b
-- title:
--   Step Data: max M from Blocks
-- statement:
--   The Step Data construction uses the max M from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L159-L164

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
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.maxM_fromBlocks {a' t' : Type*} {A : Matrix a a' k} {B : Matrix a t' k} {C : Matrix t a' k} {D : Matrix t t' k} :
    MaxM (fromBlocks A B C D) ↔ MaxM A ∧ MaxM B ∧ MaxM C ∧ MaxM D := by sorry
