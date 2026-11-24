-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_twKer_reflect
-- name    : GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:07.38563+00:00
-- url     : https://prove2.me/theorems/95276214-c239-4b39-8b6d-22b0adb3bc64
-- title:
--   Jac Exact: tw Ker reflect
-- statement:
--   The Jac Exact construction uses the tw Ker reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L166-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L166-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), IsSmooth ρ → IsSmooth σ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V →ₗ[ℂ] W), Function.Injective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    ∀ v : V, f v ∈ twKer σ N θ → v ∈ twKer ρ N θ := by sorry
