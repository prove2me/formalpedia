-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_mem_of_ind_mem
-- name    : GlobalTheory.LocMod.Inhab.mem_of_ind_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:49.968423+00:00
-- url     : https://prove2.me/theorems/4172957a-9e54-4ec8-b4c2-a30f624e3438
-- title:
--   Inhab: mem of ind mem
-- statement:
--   The Inhab construction uses the mem of ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L51-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L51-L78

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
variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}

theorem GlobalTheory.LocMod.Inhab.mem_of_ind_mem (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by sorry
