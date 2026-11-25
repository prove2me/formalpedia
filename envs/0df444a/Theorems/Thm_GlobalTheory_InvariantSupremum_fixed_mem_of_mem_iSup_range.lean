-- Prove2me | Theorems.Thm_GlobalTheory_InvariantSupremum_fixed_mem_of_mem_iSup_range
-- name    : GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:38.829844+00:00
-- url     : https://prove2.me/theorems/2cf927bb-23ee-5841-9003-813cc26765c4
-- title:
--   Invariant Supremum: fixed mem of mem i Sup range
-- statement:
--   The Invariant Supremum construction uses the fixed mem of mem i Sup range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqBotOrEqTopOfInvariant.lean#L17-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqBotOrEqTopOfInvariant.lean#L17-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqBotOrEqTopOfInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantSupremum

theorem GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (f : ι → W →ₗ[ℂ] V)
    (hf : ∀ (i : ι) (g : G) (u : W), f i (σ g u) = ρ g (f i u)) (K : Set G)
    (Z : Submodule ℂ V) (hZ : ∀ (i : ι) (v : W), (∀ k ∈ K, σ k v = v) → f i v ∈ Z)
    (_hfix : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V) (hφ : ∀ k ∈ K, ρ k φ = φ)
    (hmem : φ ∈ ⨆ i : ι, LinearMap.range (f i)) : φ ∈ Z := by sorry
