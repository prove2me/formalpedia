-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mapsInto_basePt
-- name    : GlobalTheory.RootEx.UnfoldShape.mapsInto_basePt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:00.105656+00:00
-- url     : https://prove2.me/theorems/7ffd7bb4-080c-4e70-a0d7-0ea3ca037bb2
-- title:
--   Unfold Shape: maps Into base Pt
-- statement:
--   The Unfold Shape construction uses the maps Into base Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L308-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L308-L314

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
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype n]

theorem GlobalTheory.RootEx.UnfoldShape.mapsInto_basePt {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)} {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h : MapsInto x₀ L' L) :
    MapsInto (basePt c x₀) (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by sorry
