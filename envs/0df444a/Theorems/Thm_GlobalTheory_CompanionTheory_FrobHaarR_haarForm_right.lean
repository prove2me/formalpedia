-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_right
-- name    : GlobalTheory.CompanionTheory.FrobHaarR.haarForm_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:53.818661+00:00
-- url     : https://prove2.me/theorems/cb2f3915-5d67-407c-8aba-ec309df9a6ea
-- title:
--   Frob Haar R: haar Form right
-- statement:
--   The Frob Haar R construction uses the haar Form right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L163-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L163-L175

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
variable [LocallyCompactSpace G]

theorem GlobalTheory.CompanionTheory.FrobHaarR.haarForm_right (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    haarForm μ (pullHomeo (Homeomorph.mulRight g) α) = haarForm μ α := by sorry
