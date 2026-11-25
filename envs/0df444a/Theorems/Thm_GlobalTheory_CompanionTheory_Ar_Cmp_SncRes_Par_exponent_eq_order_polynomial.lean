-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_exponent_eq_order_polynomial
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:02.117175+00:00
-- url     : https://prove2.me/theorems/95601d55-dbb4-4387-b0fd-1a536c3eca1e
-- title:
--   Par: exponent eq order polynomial
-- statement:
--   The Par construction uses the exponent eq order polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/UnitTimesParameterMonomial.lean#L46-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/UnitTimesParameterMonomial.lean#L46-L110

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_UnitTimesParameterMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by sorry
