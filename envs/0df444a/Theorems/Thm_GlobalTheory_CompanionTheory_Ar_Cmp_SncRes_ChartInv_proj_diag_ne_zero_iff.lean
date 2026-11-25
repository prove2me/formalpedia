-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_ChartInv_proj_diag_ne_zero_iff
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.proj_diag_ne_zero_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:17:42.459257+00:00
-- url     : https://prove2.me/theorems/2448c19f-64cb-4df7-87ae-ed0e5f66a9af
-- title:
--   Chart Inv: proj diag ne zero iff
-- statement:
--   The Chart Inv construction uses the proj diag ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionLocalChartPolynomial.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionLocalChartPolynomial.lean#L12-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.proj_diag_ne_zero_iff (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    SncRes.proj z ⟨k, (i, i)⟩ ≠ 0 ↔ z ⟨k, i⟩ ≠ 0 := by sorry
