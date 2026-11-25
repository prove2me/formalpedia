-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_sum_pderiv_renC
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.sum_pderiv_renC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:04.287358+00:00
-- url     : https://prove2.me/theorems/97cb8306-2fb8-5410-b764-59b0cbb90a2c
-- title:
--   Par: sum pderiv ren C
-- statement:
--   The Par construction uses the sum pderiv ren C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartParametersAtConePoint.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartParametersAtConePoint.lean#L22-L32

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SpanEqTopOfForallDotEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_BoundaryOnPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_IsRegularLocalRingLocRingOfSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsMulPowEqAevalOfMemAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsBasicOpenOfIsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartParametersAtConePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.sum_pderiv_renC {σ : Type} [Fintype σ] (t₀ : σ → ℂ) (v : Fin (Fintype.card σ) → ℂ)
    (h : MvPolynomial σ ℂ) :
    ∑ j, v j * eval (renPt t₀) (pderiv j (renC σ h)) =
      ∑ q, v (Fintype.equivFin σ q) * eval t₀ (pderiv q h) := by sorry
