-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_exists_finite_support
-- name    : GlobalTheory.CompanionTheory.PRep.JacExact.exists_finite_support
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:37.002953+00:00
-- url     : https://prove2.me/theorems/1a4bc16e-664b-4e74-8286-db46f32a65f1
-- title:
--   Jac Exact: exists finite support
-- statement:
--   The Jac Exact construction uses the exists finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L102-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L102-L125

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

theorem GlobalTheory.CompanionTheory.PRep.JacExact.exists_finite_support (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ) (x : W)
    (hx : x ∈ twKer σ N θ) :
    ∃ (s : Finset N) (t : Finset W), x ∈ Submodule.span ℂ
      {y | ∃ n ∈ s, ∃ w ∈ t, y = σ (n : G) w - ((θ n : ℂˣ) : ℂ) • w} := by sorry
