-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_ind_ne_zero
-- name    : GlobalTheory.CompanionTheory.FrobHaarR.haarForm_ind_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:15.571852+00:00
-- url     : https://prove2.me/theorems/b6dc5c0e-3ba8-40ff-8a8d-f50500325a2f
-- title:
--   Frob Haar R: haar Form ind ne zero
-- statement:
--   The Frob Haar R construction uses the haar Form ind ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L177-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L177-L185

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

theorem GlobalTheory.CompanionTheory.FrobHaarR.haarForm_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : haarForm μ (ind K hK) ≠ 0 := by sorry
