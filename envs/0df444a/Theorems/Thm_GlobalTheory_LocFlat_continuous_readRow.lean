-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_continuous_readRow
-- name    : GlobalTheory.LocFlat.continuous_readRow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:53.259946+00:00
-- url     : https://prove2.me/theorems/5de7d75d-e17a-4de9-8ca6-89ec17943d92
-- title:
--   Loc Flat: continuous read Row
-- statement:
--   The Loc Flat construction uses the continuous read Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L325-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L325-L330

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.LocFlat.continuous_readRow (p : ℕ) (hp : p - 1 < c) :
    Continuous (readRow (k := k) (n := n) (n' := n') p hp) := by sorry
