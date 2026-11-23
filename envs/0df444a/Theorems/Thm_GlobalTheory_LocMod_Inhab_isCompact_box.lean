-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_isCompact_box
-- name    : GlobalTheory.LocMod.Inhab.isCompact_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:48.209811+00:00
-- url     : https://prove2.me/theorems/3f3fe3ae-fd8c-4ffe-916d-068aa6ad3d00
-- title:
--   Inhab: is Compact box
-- statement:
--   The Inhab construction uses the is Compact box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L82-L84

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

theorem GlobalTheory.LocMod.Inhab.isCompact_box (a : kˣ) : IsCompact (box Y Y' a : Set (Matrix Y Y' k)) := by sorry
