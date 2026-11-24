-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_ind_mem
-- name    : GlobalTheory.LocMod.Inhab.ind_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:48.547541+00:00
-- url     : https://prove2.me/theorems/295d2df1-b550-4e90-94fb-6bb454eb3fc1
-- title:
--   Inhab: ind mem
-- statement:
--   The Inhab construction uses the ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L14-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L14-L49

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

theorem GlobalTheory.LocMod.Inhab.ind_mem (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by sorry
