-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_NearComp_exists_den_chPrime
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.exists_den_chPrime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:17.652071+00:00
-- url     : https://prove2.me/theorems/a348add4-3cb2-5f6d-960d-6bcf235f44d8
-- title:
--   Near Comp: exists den ch Prime
-- statement:
--   The Near Comp construction uses the exists den ch Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartRegularWithBoundaryChoice.lean#L16-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartRegularWithBoundaryChoice.lean#L16-L49

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularWithBoundaryChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.exists_den_chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : MvPolynomial (Fin m) ℂ) :
    ∃ s : MvPolynomial (Fin m) ℂ, eval t s ≠ 0 ∧ ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) →
      eval w s ≠ 0 → eval w r = 0 → ∀ g ∈ Par.chPrime I t r, eval w g = 0 := by sorry
