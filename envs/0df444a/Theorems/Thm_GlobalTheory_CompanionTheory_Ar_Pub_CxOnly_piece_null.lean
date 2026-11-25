-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxOnly_piece_null
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.piece_null
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:03:08.581216+00:00
-- url     : https://prove2.me/theorems/c0cd72af-e269-47ee-a456-95ae153e3274
-- title:
--   Cx Only: piece null
-- statement:
--   The Cx Only construction uses the piece null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/VolumeNonsimpleFibresEqZero.lean#L217-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/VolumeNonsimpleFibresEqZero.lean#L217-L277

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_ratio_smul_cons_60856f0cf16b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_segre_scaleBlock_71f3a993f711
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

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.piece_null (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hOo : IsOpen O)
    (hO : ∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
      (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))) :
    volume {y | (y, segre (γ y)) ∈ O ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} = 0 := by sorry
