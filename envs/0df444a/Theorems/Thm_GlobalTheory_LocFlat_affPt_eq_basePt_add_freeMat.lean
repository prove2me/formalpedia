-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_affPt_eq_basePt_add_freeMat
-- name    : GlobalTheory.LocFlat.affPt_eq_basePt_add_freeMat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:57.231181+00:00
-- url     : https://prove2.me/theorems/a3c1bf58-da31-4629-8f98-446ac59039da
-- title:
--   Loc Flat: aff Pt eq base Pt add free Mat
-- statement:
--   The Loc Flat construction uses the aff Pt eq base Pt add free Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L32-L34

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

theorem GlobalTheory.LocFlat.affPt_eq_basePt_add_freeMat (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e = basePt c x₀ + freeMat p e := by sorry
