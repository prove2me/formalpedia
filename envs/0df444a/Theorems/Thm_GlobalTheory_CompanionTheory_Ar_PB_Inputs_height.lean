-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Inputs_height
-- name    : GlobalTheory.CompanionTheory.Ar.PB.Inputs.height
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:28.480176+00:00
-- url     : https://prove2.me/theorems/103c1658-22fb-4846-94b1-60df0d632aa3
-- title:
--   Inputs: height
-- statement:
--   The Inputs construction uses the height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean#L330-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean#L330-L330

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GlobalTheory.CompanionTheory.Ar.PB.Inputs

theorem GlobalTheory.CompanionTheory.Ar.PB.Inputs.height (h : Inputs) : ArithmeticIntersectionNonneg := by sorry
