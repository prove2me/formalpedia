-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_stdLat
-- name    : GlobalTheory.RootEx.UnfoldShape.mem_stdLat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:57.304435+00:00
-- url     : https://prove2.me/theorems/dc4586e2-28c0-459f-9ed7-08aa0822ecf4
-- title:
--   Unfold Shape: mem std Lat
-- statement:
--   The Unfold Shape construction uses the mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L83-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RootEx.UnfoldShape.mem_stdLat {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat k ι ↔ ∀ i, v i ∈ 𝒪[k] := by sorry
