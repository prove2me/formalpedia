-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_not_eventually_prod_eq_zero
-- name    : GlobalTheory.CompanionTheory.ComplexSets.not_eventually_prod_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:32.037806+00:00
-- url     : https://prove2.me/theorems/da13b58e-8dab-4be3-b246-6ac7a5314a3a
-- title:
--   Complex Sets: not eventually prod eq zero
-- statement:
--   The Complex Sets construction uses the not eventually prod eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L32-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L32-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
variable {σ : Type} [Fintype σ]

theorem GlobalTheory.CompanionTheory.ComplexSets.not_eventually_prod_eq_zero {ι : Type} {Y : Set (σ → ℂ)} {w : σ → ℂ}
    (hY : GermIrreducibleAt Y w) (φ : ι → (σ → ℂ) → ℂ) (s : Finset ι)
    (hφ : ∀ j ∈ s, AnalyticAt ℂ (φ j) w)
    (hne : ∀ j ∈ s, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ j z = 0) :
    ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → ∏ j ∈ s, φ j z = 0 := by sorry
