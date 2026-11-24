-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_invariant_of_tsupport
-- name    : GlobalTheory.LocMod.Inhab.invariant_of_tsupport
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:05.649239+00:00
-- url     : https://prove2.me/theorems/ae62b02e-8459-4360-8584-7e89f322b8a9
-- title:
--   Inhab: invariant of tsupport
-- statement:
--   The Inhab construction uses the invariant of tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L125-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem GlobalTheory.LocMod.Inhab.invariant_of_tsupport {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by sorry
