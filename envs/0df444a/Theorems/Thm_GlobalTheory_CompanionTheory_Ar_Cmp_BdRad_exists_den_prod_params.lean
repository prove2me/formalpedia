-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_exists_den_prod_params
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:39.593812+00:00
-- url     : https://prove2.me/theorems/80411784-0461-4bd7-8581-fe7871307e7a
-- title:
--   Bd Rad: exists den prod params
-- statement:
--   The Bd Rad construction uses the exists den prod params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L110-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L110-L198

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

theorem GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by sorry
