-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxOnly_smul_mem_fibre
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.smul_mem_fibre
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:31.218391+00:00
-- url     : https://prove2.me/theorems/070942c8-6fb1-4d57-97ce-e0ac730c1f61
-- title:
--   Cx Only: smul mem fibre
-- statement:
--   The Cx Only construction uses the smul mem fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/VolumeNonsimpleFibresEqZero.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/VolumeNonsimpleFibresEqZero.lean#L39-L45

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
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_VolumeNonsimpleFibresEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_proj_segre_36c3e8284232
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_ratio_f91644499ea4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_inv_smul_eq_cons_954153cdf7f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_not_injective_of_coord_eventually_const_10457ccc6c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_ratio_smul_cons_60856f0cf16b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_segre_scaleBlock_71f3a993f711
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_swapProj_apply_8d95c3de703d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxOnly
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull (ratio inv_smul_eq_cons ratio_smul_cons segre_scaleBlock
  differentiableAt_proj_segre differentiableAt_ratio swapProj swapProj_apply
  not_injective_of_coord_eventually_const)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.smul_mem_fibre {Q : Ideal (MRingOver ℂ ι)} (hQh : IsMultiHomogIdeal Q) [Nonempty K] {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ conePts Q) (Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (h0 : Ψ' (segre z) 0 ≠ 0) :
    (Ψ' (segre z) 0)⁻¹ • segre z ∈ setFibre (conePts Q) Ψ' (ratio (Ψ' (segre z))) := by sorry
