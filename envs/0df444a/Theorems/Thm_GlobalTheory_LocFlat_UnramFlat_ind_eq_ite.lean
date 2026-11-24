-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_ind_eq_ite
-- name    : GlobalTheory.LocFlat.UnramFlat.ind_eq_ite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:51.698813+00:00
-- url     : https://prove2.me/theorems/dfa4bd15-e429-4f51-834a-b98d79674152
-- title:
--   Unram Flat: ind eq ite
-- statement:
--   The Unram Flat construction uses the ind eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L216-L219

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n]
open Classical

theorem GlobalTheory.LocFlat.UnramFlat.ind_eq_ite {m m' : Type} (x : Matrix m m' k) :
    Set.indicator {x : Matrix m m' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) x = if IntM x then 1 else 0 := by sorry
