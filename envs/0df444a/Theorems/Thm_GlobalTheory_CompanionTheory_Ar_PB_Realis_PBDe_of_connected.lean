-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_PBDe_of_connected
-- name    : GlobalTheory.CompanionTheory.Ar.PB.Realis.PBDe_of_connected
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:33.676504+00:00
-- url     : https://prove2.me/theorems/923f0ec8-9fe4-4b44-a3c4-7f90f9749e71
-- title:
--   Realis: PBDe of connected
-- statement:
--   The Realis construction uses the PBDe of connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean#L198-L200

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
open GlobalTheory.CompanionTheory.Ar.PB.Realis
variable {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (II : IntersectionSystem)

theorem GlobalTheory.CompanionTheory.Ar.PB.Realis.PBDe_of_connected [Fintype σ] [ConnectedSpace S.X] :
    Re.de = Re.deg ∧ Re.PBDe II = Re.PB II ∧ ∀ t, Re.FTDe II t = Re.FT II t := by sorry
