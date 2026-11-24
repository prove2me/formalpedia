-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_inX_mem_chainLat
-- name    : GlobalTheory.RootEx.UnfoldShape.inX_mem_chainLat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:56.801478+00:00
-- url     : https://prove2.me/theorems/47ddbba6-324b-4b29-a55e-eefe7cd7a235
-- title:
--   Unfold Shape: in X mem chain Lat
-- statement:
--   The Unfold Shape construction uses the in X mem chain Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L140-L143

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
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n]

theorem GlobalTheory.RootEx.UnfoldShape.inX_mem_chainLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n → k} :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔ v ∈ L := by sorry
