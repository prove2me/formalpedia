-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_flCol_smul
-- name    : GlobalTheory.LocFlat.flCol_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:16.984479+00:00
-- url     : https://prove2.me/theorems/1eceb2dc-43e6-483f-b1db-1a6375cf3e51
-- title:
--   Loc Flat: fl Col smul
-- statement:
--   The Loc Flat construction uses the fl Col smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFactorThroughFlatMapFourierJacobiColumn.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFactorThroughFlatMapFourierJacobiColumn.lean#L51-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.LocFlat.flCol_smul (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flCol ψ ν p (a • Φ) = a • flCol ψ ν p Φ := by sorry
