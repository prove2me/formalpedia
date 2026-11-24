-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_exists_coeff
-- name    : GlobalTheory.CompanionTheory.FrobHaarR.exists_coeff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:50.061934+00:00
-- url     : https://prove2.me/theorems/73de8b0b-12b3-42ee-a0e5-dd3cabfa3a0f
-- title:
--   Frob Haar R: exists coeff
-- statement:
--   The Frob Haar R construction uses the exists coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L121-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L121-L130

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.FrobHaarR.exists_coeff (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ s : ℂ, ∀ M : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), M (pullHomeo (Homeomorph.mulRight g) α) = M α) →
        M f = s * M (ind K hK) := by sorry
