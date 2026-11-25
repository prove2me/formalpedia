-- Prove2me | Theorems.Thm_GlobalTheory_T_regular_system_of_parameters_local_ring_alt
-- name    : GlobalTheory.T.regular_system_of_parameters_local_ring_alt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:44:35.826265+00:00
-- url     : https://prove2.me/theorems/422835c7-8f59-5973-83e1-fc90275436a9
-- title:
--   T: regular system of parameters local ring alt
-- statement:
--   The T construction uses the regular system of parameters local ring alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRingAltBis.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRingAltBis.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_PrimesBelowParams
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRingAltBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.regular_system_of_parameters_local_ring_alt : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by sorry
