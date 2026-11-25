-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dehom_coeff_mul_eq_zero
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.coeff_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:04.341184+00:00
-- url     : https://prove2.me/theorems/b83aa8f0-316d-435b-af71-ba0824841cd8
-- title:
--   Dehom: coeff mul eq zero
-- statement:
--   The Dehom construction uses the coeff mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L67-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L67-L78

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.coeff_mul_eq_zero {r f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hr : ∀ m ∈ r.support, mdeg m ≠ b) (hf : IsMultiHomog f a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : mdeg m = b + a) : coeff m (r * f) = 0 := by sorry
