-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_rowAt_disj
-- name    : GlobalTheory.LocFlat.UnramFlat.rowAt_disj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:43.893783+00:00
-- url     : https://prove2.me/theorems/c781ed97-d746-43ef-b4fa-c2dc392d6f49
-- title:
--   Unram Flat: row At disj
-- statement:
--   The Unram Flat construction uses the row At disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L74-L84

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

theorem GlobalTheory.LocFlat.UnramFlat.rowAt_disj (x₀ : Matrix n n' k) (e) (u : n' → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) :
    rowAt n c p u r s = 0 ∨ affPt (c := c) p x₀ e r s = 0 := by sorry
