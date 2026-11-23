-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_sep
-- name    : GlobalTheory.LocMod.Inhab.exists_sep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:44.151297+00:00
-- url     : https://prove2.me/theorems/f3eafca1-587a-43bf-8b03-40d412feeb71
-- title:
--   Inhab: exists sep
-- statement:
--   The Inhab construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L132-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L132-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
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

theorem GlobalTheory.LocMod.Inhab.exists_sep {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) (a : kˣ) {u : Matrix Y Y' k}
    (hu : u ∉ box Y Y' a) : ∃ y ∈ box Y Y' (d / a), pairing ψ u y ≠ 1 := by sorry
