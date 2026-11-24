-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_exists_clopen_ch_near
-- name    : GlobalTheory.LocFlat.exists_clopen_ch_near
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:06.204031+00:00
-- url     : https://prove2.me/theorems/31027e5e-972e-40fd-87d7-78cb72e31abd
-- title:
--   Loc Flat: exists clopen ch near
-- statement:
--   The Loc Flat construction uses the exists clopen ch near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L67-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L67-L88

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

theorem GlobalTheory.LocFlat.exists_clopen_ch_near (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ W : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsClopen W ∧ IsCompact W ∧
      (0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∈ W ∧
      ∀ z ∈ W, ‖((ψ (-ch z) : Circle) : ℂ) - 1‖ < 1 / 2 := by sorry
