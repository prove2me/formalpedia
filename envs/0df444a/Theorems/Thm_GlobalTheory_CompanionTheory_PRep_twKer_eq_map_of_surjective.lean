-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_twKer_eq_map_of_surjective
-- name    : GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:56.742931+00:00
-- url     : https://prove2.me/theorems/1ddd656c-7b40-4153-bee3-d0befeb14656
-- title:
--   PRep: tw Ker eq map of surjective
-- statement:
--   The PRep construction uses the tw Ker eq map of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwKerEqMapOfSurjective.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwKerEqMapOfSurjective.lean#L8-L21

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

theorem GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (N : Subgroup G) (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hint : ∀ g v, f (ρ g v) = σ g (f v)) : twKer σ N θ = (twKer ρ N θ).map f := by sorry
