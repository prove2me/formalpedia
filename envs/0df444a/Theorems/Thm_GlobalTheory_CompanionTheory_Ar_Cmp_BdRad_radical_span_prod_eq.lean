-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_radical_span_prod_eq
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.radical_span_prod_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:39.959998+00:00
-- url     : https://prove2.me/theorems/110a82cf-2008-4da5-b300-dcdd0c39ce17
-- title:
--   Bd Rad: radical span prod eq
-- statement:
--   The Bd Rad construction uses the radical span prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L80-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L80-L102

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
variable {m : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.radical_span_prod_eq {O ι : Type*} [CommRing O] [IsDomain O] (R : ι → O) (J : Finset ι)
    (hpr : ∀ i, Prime (R i)) (hna : ∀ i j, i ≠ j → ¬ Associated (R i) (R j)) :
    (Ideal.span {∏ i ∈ J, R i}).radical = Ideal.span {∏ i ∈ J, R i} := by sorry
