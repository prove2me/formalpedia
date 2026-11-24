-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_dominant_of_open
-- name    : GlobalTheory.CompanionTheory.ComplexSets.dominant_of_open
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:16.059724+00:00
-- url     : https://prove2.me/theorems/04e2b46f-8ec3-4de2-8bd9-aadc2a21e9b5
-- title:
--   Complex Sets: dominant of open
-- statement:
--   The Complex Sets construction uses the dominant of open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L80-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L80-L139

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

theorem GlobalTheory.CompanionTheory.ComplexSets.dominant_of_open {ι : Type} [Fintype ι] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    {S W : Set (σ → ℂ)} {w : σ → ℂ} (Y : ι → Set (σ → ℂ))
    (hopen : ∀ x ∈ S, ∀ V ∈ 𝓝 x, A '' (S ∩ V) ∈ 𝓝 (A x))
    (hYan : ∀ i, IsAnalyticNear (Y i) w) (hYirr : ∀ i, GermIrreducibleAt (Y i) w)
    (hno : ∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j)
    (hW : W ∈ 𝓝 w) (hS : S ∩ W = (⋃ i, Y i) ∩ W) (i : ι)
    (h : (Fin d → ℂ) → ℂ) (hh : AnalyticAt ℂ h (A w))
    (hv : ∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) :
    ∀ᶠ y in 𝓝 (A w), h y = 0 := by sorry
