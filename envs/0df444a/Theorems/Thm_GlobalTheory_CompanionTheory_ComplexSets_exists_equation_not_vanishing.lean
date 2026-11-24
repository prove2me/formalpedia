-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_exists_equation_not_vanishing
-- name    : GlobalTheory.CompanionTheory.ComplexSets.exists_equation_not_vanishing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:00.242698+00:00
-- url     : https://prove2.me/theorems/a5dd61fe-71fb-4b1d-beb8-87aecc0ef24b
-- title:
--   Complex Sets: exists equation not vanishing
-- statement:
--   The Complex Sets construction uses the exists equation not vanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L11-L30

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

theorem GlobalTheory.CompanionTheory.ComplexSets.exists_equation_not_vanishing {Y Z : Set (σ → ℂ)} {w : σ → ℂ} (hZ : IsAnalyticNear Z w)
    (hYZ : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) :
    ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (∀ᶠ z in 𝓝 w, z ∈ Z → φ z = 0) ∧
      ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 := by sorry
