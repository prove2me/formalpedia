-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_apply
-- name    : GlobalTheory.CompanionTheory.FrobHaarR.haarForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:41.708826+00:00
-- url     : https://prove2.me/theorems/4b061cf2-8f5e-4c58-bc42-139810f15d6f
-- title:
--   Frob Haar R: haar Form apply
-- statement:
--   The Frob Haar R construction uses the haar Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L148-L150

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
  [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.CompanionTheory.FrobHaarR.haarForm_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    haarForm μ α = ∫ x, (α : G → ℂ) x ∂μ := by sorry
