-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_intM_colAt
-- name    : GlobalTheory.LocFlat.UnramFlat.intM_colAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:58.344086+00:00
-- url     : https://prove2.me/theorems/f8a163c3-41c2-4d94-b59c-a309ede5cd0b
-- title:
--   Unram Flat: int M col At
-- statement:
--   The Unram Flat construction uses the int M col At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L34-L46

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
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c p : ℕ}

theorem GlobalTheory.LocFlat.UnramFlat.intM_colAt (y : n → k) :
    IntM (colAt (k := k) n' c p y) ↔ ∀ i : Fin (c + 1), i.val + 1 = p → ∀ r, y r ∈ 𝒪[k] := by sorry
