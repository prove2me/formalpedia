-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_ind_box_mem
-- name    : GlobalTheory.LocMod.Inhab.ind_box_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:46.679211+00:00
-- url     : https://prove2.me/theorems/63c2ee5d-0640-444e-bd05-c684f1f883df
-- title:
--   Inhab: ind box mem
-- statement:
--   The Inhab construction uses the ind box mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L158-L165

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

theorem GlobalTheory.LocMod.Inhab.ind_box_mem (a : kˣ) : ind (box Y Y' a) ∈ SB (Matrix Y Y' k) := by sorry
