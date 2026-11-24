-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_exists_hypersurface_of_monic_relation
-- name    : GlobalTheory.CompanionTheory.ComplexSets.exists_hypersurface_of_monic_relation
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:12.236685+00:00
-- url     : https://prove2.me/theorems/a852589a-ee5f-4b95-9275-d7eac874069d
-- title:
--   Complex Sets: exists hypersurface of monic relation
-- statement:
--   The Complex Sets construction uses the exists hypersurface of monic relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeetOverHypersurfaceOfGerm.lean#L9-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeetOverHypersurfaceOfGerm.lean#L9-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

theorem GlobalTheory.CompanionTheory.ComplexSets.exists_hypersurface_of_monic_relation {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hirr : GermIrreducibleAt Y w) {φ : (σ → ℂ) → ℂ}
    (hφ : AnalyticAt ℂ φ w) (hnv : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0) :
    ∀ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ Y → φ z ^ N + ∑ j, a j (A z) * φ z ^ (j : ℕ) = 0) →
      ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 → e (A z) = 0 := by sorry
