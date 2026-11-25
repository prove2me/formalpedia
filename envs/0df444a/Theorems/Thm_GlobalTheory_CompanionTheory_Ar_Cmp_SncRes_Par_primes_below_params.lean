-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_primes_below_params
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:31.917329+00:00
-- url     : https://prove2.me/theorems/1078a82d-dcfc-5057-a14c-373ed6f6fabc
-- title:
--   Par: primes below params
-- statement:
--   The Par construction uses the primes below params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/PrimesBelowParams.lean#L66-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/PrimesBelowParams.lean#L66-L104

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_PrimesBelowParams
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp
variable {m : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by sorry
