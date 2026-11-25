-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_exists_form
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.exists_form
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:07.592934+00:00
-- url     : https://prove2.me/theorems/311f095e-3ab5-497d-9e35-20f7e10ab347
-- title:
--   Dict: exists form
-- statement:
--   The Dict construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L79-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L79-L111

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.exists_form (p : (k : K) → ι k) (I : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (hI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ I) (g : MvPolynomial (Σ k, ι k) ℂ) :
    ∃ (d : K → ℕ) (H : MvPolynomial (Σ k, ι k) ℂ), IsMultiHomog H d ∧ H - g ∈ I := by sorry
