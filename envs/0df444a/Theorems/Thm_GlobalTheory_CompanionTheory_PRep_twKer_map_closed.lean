-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_twKer_map_closed
-- name    : GlobalTheory.CompanionTheory.PRep.twKer_map_closed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:20.773712+00:00
-- url     : https://prove2.me/theorems/094d0e89-7d52-477f-9986-9507e1dd8619
-- title:
--   PRep: tw Ker map closed
-- statement:
--   The PRep construction uses the tw Ker map closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwKerEqMapOfSurjective.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwKerEqMapOfSurjective.lean#L23-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwKerEqMapOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep

theorem GlobalTheory.CompanionTheory.PRep.twKer_map_closed : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W), Function.Surjective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    twKer σ N θ = (twKer ρ N θ).map f := by sorry
