-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_glue_restOf
-- name    : GlobalTheory.LocFlat.glue_restOf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:53.805007+00:00
-- url     : https://prove2.me/theorems/605edf06-dd13-4f4c-a6b9-56095286b017
-- title:
--   Loc Flat: glue rest Of
-- statement:
--   The Loc Flat construction uses the glue rest Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L230-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L230-L237

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

theorem GlobalTheory.LocFlat.glue_restOf {X : Type} (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool)
    (E : X → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X)
    (hER : ∀ z r s, rd r s = true → E (R z) r s = z r s) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    glue rd E (R z, restOf rd z) = z := by sorry
