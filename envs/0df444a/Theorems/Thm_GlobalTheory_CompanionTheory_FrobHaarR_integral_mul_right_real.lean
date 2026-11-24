-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_integral_mul_right_real
-- name    : GlobalTheory.CompanionTheory.FrobHaarR.integral_mul_right_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:57.968373+00:00
-- url     : https://prove2.me/theorems/b93943b5-9af1-43fb-aae4-7cf26dbcd123
-- title:
--   Frob Haar R: integral mul right real
-- statement:
--   The Frob Haar R construction uses the integral mul right real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L154-L161

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

theorem GlobalTheory.CompanionTheory.FrobHaarR.integral_mul_right_real (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G)
    {u : G → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) :
    ∫ x, u (x * g) ∂μ = ∫ x, u x ∂μ := by sorry
