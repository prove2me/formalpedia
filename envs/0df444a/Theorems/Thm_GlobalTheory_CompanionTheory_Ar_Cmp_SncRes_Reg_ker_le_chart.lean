-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_ker_le_chart
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.ker_le_chart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:31:30.94838+00:00
-- url     : https://prove2.me/theorems/7aea9eab-bc81-5793-a3ec-941b5cb12fa3
-- title:
--   Reg: ker le chart
-- statement:
--   The Reg construction uses the ker le chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L90-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L90-L109

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.ker_le_chart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (g : MvPolynomial (Σ k, ι k) ℚ)
    (hg : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) g = 0) :
    map (algebraMap ℚ ℂ) g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by sorry
