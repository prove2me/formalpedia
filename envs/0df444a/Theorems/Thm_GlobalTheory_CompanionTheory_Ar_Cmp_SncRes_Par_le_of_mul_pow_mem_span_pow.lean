-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_le_of_mul_pow_mem_span_pow
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.le_of_mul_pow_mem_span_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:17:07.981018+00:00
-- url     : https://prove2.me/theorems/b2caf6b9-f611-41c0-94b0-84a1611493f0
-- title:
--   Par: le of mul pow mem span pow
-- statement:
--   The Par construction uses the le of mul pow mem span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/UnitTimesParameterMonomial.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/UnitTimesParameterMonomial.lean#L14-L21

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.le_of_mul_pow_mem_span_pow {O : Type*} [CommRing O] [IsDomain O] {p a : O} (hp : Prime p)
    (ha : ¬ p ∣ a) {k n : ℕ} (h : a * p ^ k ∈ Ideal.span {p} ^ n) : n ≤ k := by sorry
