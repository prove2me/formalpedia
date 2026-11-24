-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_fixed
-- name    : GlobalTheory.LocMod.Inhab.exists_fixed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:38.611804+00:00
-- url     : https://prove2.me/theorems/d9b15fc8-6780-434b-9d65-c854ccba41da
-- title:
--   Inhab: exists fixed
-- statement:
--   The Inhab construction uses the exists fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L11-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean#L11-L64

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

theorem GlobalTheory.LocMod.Inhab.exists_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] {χ : G → G → ℂ} (h : IsBichar χ)
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ y f, σ y f = 0 → f = 0)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f)) (L K : AddSubgroup G) [Finite (L ⧸ K.addSubgroupOf L)]
    (hsep : ∀ u ∈ L, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (P : Submodule ℂ V)
    (hP : ∀ u ∈ L, ∀ f ∈ P, ρ u f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {f : V} (hf : f ∈ P) (f0 : f ≠ 0)
    (hK : ∀ κ ∈ K, ρ κ f = f) : ∃ g ∈ P, g ≠ 0 ∧ ∀ u ∈ L, ρ u g = g := by sorry
