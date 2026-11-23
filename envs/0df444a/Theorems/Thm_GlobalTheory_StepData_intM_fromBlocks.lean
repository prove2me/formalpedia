-- Prove2me | Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
-- name    : GlobalTheory.StepData.intM_fromBlocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:17.019812+00:00
-- url     : https://prove2.me/theorems/0b15a3b4-3bcc-49e6-baa9-7d7cc37aaa1a
-- title:
--   Step Data: int M from Blocks
-- statement:
--   The Step Data construction uses the int M from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L151-L156

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

theorem GlobalTheory.StepData.intM_fromBlocks {a' t' : Type*} {A : Matrix a a' k} {B : Matrix a t' k} {C : Matrix t a' k} {D : Matrix t t' k} :
    IntM (fromBlocks A B C D) ↔ IntM A ∧ IntM B ∧ IntM C ∧ IntM D := by sorry
