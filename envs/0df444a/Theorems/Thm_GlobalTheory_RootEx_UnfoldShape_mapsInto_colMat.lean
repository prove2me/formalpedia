-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mapsInto_colMat
-- name    : GlobalTheory.RootEx.UnfoldShape.mapsInto_colMat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:50.498614+00:00
-- url     : https://prove2.me/theorems/e8e7c889-0462-4706-ad6b-1ad834727767
-- title:
--   Unfold Shape: maps Into col Mat
-- statement:
--   The Unfold Shape construction uses the maps Into col Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L289-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L289-L305

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
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype n] [DecidableEq n]

theorem GlobalTheory.RootEx.UnfoldShape.mapsInto_colMat {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)}
    {Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, (ϖ : k) ^ (i.val + 2) • y i ∈ Λ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.MapsInto (_root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ (c + 1) L') Λ := by sorry
