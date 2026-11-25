-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_eq_zero_iff
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.theta_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:17.265988+00:00
-- url     : https://prove2.me/theorems/7a1e8ff3-55df-5788-a462-63c9fa73565d
-- title:
--   Dict: theta eq zero iff
-- statement:
--   The Dict construction uses the theta eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L174-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean#L174-L183

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.theta_eq_zero_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) :
    theta Q p f = 0 ↔ f ∈ Q := by sorry
