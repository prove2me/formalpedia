-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_ideal_isPrime_and_mem_iff
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:15:58.394226+00:00
-- url     : https://prove2.me/theorems/13df97da-1882-51ce-ba8b-61479ff419e6
-- title:
--   Dict: ideal is Prime and mem iff
-- statement:
--   The Dict construction uses the ideal is Prime and mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L250-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L250-L261

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
      (SncRes.ideal Q p).IsPrime ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
        (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by sorry
