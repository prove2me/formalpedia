-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_map_ptIdeal_eq_maximalIdeal_ordAff
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.map_ptIdeal_eq_maximalIdeal_ordAff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:45.373802+00:00
-- url     : https://prove2.me/theorems/3e43af18-f2d7-5fa5-8a47-6a7f4ad7c200
-- title:
--   Par: map pt Ideal eq maximal Ideal ord Aff
-- statement:
--   The Par construction uses the map pt Ideal eq maximal Ideal ord Aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/UnitTimesParameterMonomial.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/UnitTimesParameterMonomial.lean#L23-L44

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.map_ptIdeal_eq_maximalIdeal_ordAff {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by sorry
