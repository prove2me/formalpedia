-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dehom_lift_sub_mem
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.lift_sub_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:34.234889+00:00
-- url     : https://prove2.me/theorems/aa06e02a-13a2-49a7-98d6-b9d317d2d05b
-- title:
--   Dehom: lift sub mem
-- statement:
--   The Dehom construction uses the lift sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L127-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L127-L144

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerFromAffineChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_exists_blockComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_isMultiHomogIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.lift_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (q : Σ k, ι k) :
    lift p q - renR (Σ k, ι k) (X q) ∈ ideal S p := by sorry
