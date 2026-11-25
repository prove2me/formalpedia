-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_map_ptIdeal_eq_maximalIdeal
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.map_ptIdeal_eq_maximalIdeal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:18.224621+00:00
-- url     : https://prove2.me/theorems/28281619-10b2-43b1-a5c5-6278e4c1ded0
-- title:
--   Par: map pt Ideal eq maximal Ideal
-- statement:
--   The Par construction uses the map pt Ideal eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/PrimesBelowParams.lean#L23-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/PrimesBelowParams.lean#L23-L45

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.map_ptIdeal_eq_maximalIdeal {I : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by sorry
