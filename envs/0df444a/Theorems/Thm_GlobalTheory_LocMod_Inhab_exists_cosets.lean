-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_cosets
-- name    : GlobalTheory.LocMod.Inhab.exists_cosets
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:46.362136+00:00
-- url     : https://prove2.me/theorems/d95204b8-8cf0-49df-a138-30a0b07f770e
-- title:
--   Inhab: exists cosets
-- statement:
--   The Inhab construction uses the exists cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L134-L138

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

theorem GlobalTheory.LocMod.Inhab.exists_cosets {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by sorry
