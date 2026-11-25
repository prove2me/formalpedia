-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_KerChart_exists_int_clear
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.exists_int_clear
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:15:05.244538+00:00
-- url     : https://prove2.me/theorems/2d5edb60-5af6-5c4c-ad33-4ce339defd66
-- title:
--   Ker Chart: exists int clear
-- statement:
--   The Ker Chart construction uses the exists int clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MapMemChartIdealOfAevalEqZero.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MapMemChartIdealOfAevalEqZero.lean#L13-L31

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
open MvPolynomial ReciprocityTheory.AnForm.R
variable {σ : Type}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.exists_int_clear (G : MvPolynomial σ ℚ) :
    ∃ (n : ℤ) (G₀ : MvPolynomial σ ℤ), n ≠ 0 ∧
      map (Int.castRingHom ℚ) G₀ = C (n : ℚ) * G := by sorry
