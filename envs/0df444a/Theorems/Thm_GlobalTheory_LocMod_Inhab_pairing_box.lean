-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_box
-- name    : GlobalTheory.LocMod.Inhab.pairing_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:03.350088+00:00
-- url     : https://prove2.me/theorems/e532c302-401a-4c90-97cf-d935e28e5ab9
-- title:
--   Inhab: pairing box
-- statement:
--   The Inhab construction uses the pairing box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L157-L162

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

theorem GlobalTheory.LocMod.Inhab.pairing_box {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {a : kˣ} {u y : Matrix Y Y' k}
    (hu : u ∈ box Y Y' a) (hy : y ∈ box Y Y' (d / a)) : pairing ψ u y = 1 := by sorry
