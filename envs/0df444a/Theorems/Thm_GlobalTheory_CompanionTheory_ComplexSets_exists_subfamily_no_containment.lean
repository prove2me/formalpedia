-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_exists_subfamily_no_containment
-- name    : GlobalTheory.CompanionTheory.ComplexSets.exists_subfamily_no_containment
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:16.511529+00:00
-- url     : https://prove2.me/theorems/91a246a5-7690-49ea-9105-5862de3402c1
-- title:
--   Complex Sets: exists subfamily no containment
-- statement:
--   The Complex Sets construction uses the exists subfamily no containment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L53-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean#L53-L78

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

theorem GlobalTheory.CompanionTheory.ComplexSets.exists_subfamily_no_containment {ι : Type} [Finite ι] (Y : ι → Set (σ → ℂ)) (w : σ → ℂ) :
    ∃ T : Finset ι, (∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i) ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j := by sorry
