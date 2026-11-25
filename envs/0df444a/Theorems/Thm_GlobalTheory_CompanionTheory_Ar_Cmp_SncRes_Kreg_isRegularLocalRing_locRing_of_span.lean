-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Kreg_isRegularLocalRing_locRing_of_span
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg.isRegularLocalRing_locRing_of_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:04.118839+00:00
-- url     : https://prove2.me/theorems/643ea1ec-0aa8-5b3d-937d-a44647543347
-- title:
--   Kreg: is Regular Local Ring loc Ring of span
-- statement:
--   The Kreg construction uses the is Regular Local Ring loc Ring of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/IsRegularLocalRingLocRingOfSpan.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/IsRegularLocalRingLocRingOfSpan.lean#L10-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_IsRegularLocalRingLocRingOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg.isRegularLocalRing_locRing_of_span :
    ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
      (r : Fin e → MvPolynomial (Fin m) ℂ), (∀ h ∈ I, eval t h = 0) →
      ringKrullDim (locRing I t) = e →
      Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
        Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) →
      IsRegularLocalRing (locRing I t) := by sorry
