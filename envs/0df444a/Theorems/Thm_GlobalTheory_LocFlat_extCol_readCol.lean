-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_extCol_readCol
-- name    : GlobalTheory.LocFlat.extCol_readCol
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:05.392405+00:00
-- url     : https://prove2.me/theorems/0fa9f24b-ca2f-4780-bdc5-8bfe071216c8
-- title:
--   Loc Flat: ext Col read Col
-- statement:
--   The Loc Flat construction uses the ext Col read Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L268-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L268-L276

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

theorem GlobalTheory.LocFlat.extCol_readCol (p : ℕ) (hp : p - 1 < c + 1) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s)
    (h : rdCol p r s = true) : extCol (readCol p hp z) r s = z r s := by sorry
