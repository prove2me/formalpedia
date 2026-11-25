-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxTwist_exists_dominating_twist
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:39.685937+00:00
-- url     : https://prove2.me/theorems/f7d25969-d4ec-5562-9bb1-64a4afb231a6
-- title:
--   Cx Twist: exists dominating twist
-- statement:
--   The Cx Twist construction uses the exists dominating twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsSmoothMetricsNonnegDensity.lean#L32-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsSmoothMetricsNonnegDensity.lean#L32-L75

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MemChartComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosDensIntegrable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsSmoothMetricsNonnegDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxTwist

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by sorry
