-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dehom_map_deh_le
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.map_deh_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:01.574998+00:00
-- url     : https://prove2.me/theorems/b8b5547c-6d99-5f1e-b26a-6589968f4332
-- title:
--   Dehom: map deh le
-- statement:
--   The Dehom construction uses the map deh le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean#L165-L172

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.map_deh_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal.map (bind₁ (lift p) : _ →ₐ[ℂ] _) S ≤ ideal S p := by sorry
