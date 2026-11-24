-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_starProjection_comm
-- name    : GlobalTheory.CompanionTheory.AdmGL.starProjection_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:43.181148+00:00
-- url     : https://prove2.me/theorems/5c849db3-6d50-459f-b5d0-445ee37f8865
-- title:
--   Adm GL: star Projection comm
-- statement:
--   The Adm GL construction uses the star Projection comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L22-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L22-L37

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.CompanionTheory.AdmGL.starProjection_comm {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) (R : Submodule ℂ H)
    [FiniteDimensional ℂ R] (hR : ∀ k, ∀ w ∈ R, π k w ∈ R) (k : K) (x : H) :
    R.starProjection (π k x) = π k (R.starProjection x) := by sorry
