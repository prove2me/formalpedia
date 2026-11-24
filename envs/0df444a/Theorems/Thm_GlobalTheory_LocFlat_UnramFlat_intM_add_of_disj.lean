-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_intM_add_of_disj
-- name    : GlobalTheory.LocFlat.UnramFlat.intM_add_of_disj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:24.013577+00:00
-- url     : https://prove2.me/theorems/5ab814fc-d34c-4f22-a776-0dc3d5741980
-- title:
--   Unram Flat: int M add of disj
-- statement:
--   The Unram Flat construction uses the int M add of disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L20-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LocFlat.UnramFlat.intM_add_of_disj {m m' : Type} {A B : Matrix m m' k} (h : ∀ r s, B r s = 0 ∨ A r s = 0) :
    IntM (A + B) ↔ IntM A ∧ IntM B := by sorry
