-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_pow
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.isMultiHomog_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:17.862466+00:00
-- url     : https://prove2.me/theorems/99910eab-a0c7-4bfe-9797-a5c72ebb565c
-- title:
--   Dict: is Multi Homog pow
-- statement:
--   The Dict construction uses the is Multi Homog pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L54-L60

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.isMultiHomog_pow {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (n : ℕ) : IsMultiHomog (f ^ n) (n • a) := by sorry
