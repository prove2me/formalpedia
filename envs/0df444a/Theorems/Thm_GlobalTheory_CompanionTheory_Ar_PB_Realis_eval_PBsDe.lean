-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_eval_PBsDe
-- name    : GlobalTheory.CompanionTheory.Ar.PB.Realis.eval_PBsDe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:57.056233+00:00
-- url     : https://prove2.me/theorems/a63e8f62-d9da-4da7-95d3-447fff322703
-- title:
--   Realis: eval PBs De
-- statement:
--   The Realis construction uses the eval PBs De property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean#L264-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean#L264-L267

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
variable {D N : ℕ} {Ψ : Type} [Fintype Ψ] {S : AnSys D (Option (Ψ × Fin N))} {P : Ideal (MRing ι)}
  (Re : Realis S P) (II : IntersectionSystem)

theorem GlobalTheory.CompanionTheory.Ar.PB.Realis.eval_PBsDe (k : ℕ) (lam : Ψ × Fin N → ℝ) (s : ℝ) :
    eval (fun o => o.elim s lam) (Re.PBsDe II k) = eval (fun o => o.elim (s / k) lam) (Re.PBs II) / S.nComp := by sorry
