-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxPosMeas_setSheetIndep
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.setSheetIndep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:21:53.671198+00:00
-- url     : https://prove2.me/theorems/987b9036-d9df-47e4-8a64-e13e8872e9b9
-- title:
--   Cx Pos Meas: set Sheet Indep
-- statement:
--   The Cx Pos Meas construction uses the set Sheet Indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AemeasurableCxPosDensity.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AemeasurableCxPosDensity.lean#L151-L162

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AemeasurableCxPosDensity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
open MvPolynomial MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
  GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open ReciprocityTheory.AnForm.R (conePts)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.setSheetIndep {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ᵐ y : Fin e → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      IsSetSheet S Ψ y w γ → IsSetSheet S Ψ y w γ' →
      maDensity (fun j y' => pot L j (γ y')) y = maDensity (fun j y' => pot L j (γ' y')) y := by sorry
