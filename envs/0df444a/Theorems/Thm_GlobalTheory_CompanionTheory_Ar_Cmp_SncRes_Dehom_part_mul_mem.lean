-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dehom_part_mul_mem
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.part_mul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:03.670697+00:00
-- url     : https://prove2.me/theorems/68504e87-dbd7-45a2-af9b-d426951c9e07
-- title:
--   Dehom: part mul mem
-- statement:
--   The Dehom construction uses the part mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L82-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L82-L107

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.part_mul_mem [DecidableEq K] {I : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hI : ∀ k, I.IsHomogeneous (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)))
    {s f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (h : s * f ∈ I)
    (b : K → ℕ) : part b s * f ∈ I := by sorry
