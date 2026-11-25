-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isIntegralClosure_dedekind
-- name    : GlobalTheory.finite_of_isIntegralClosure_dedekind
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:41.810585+00:00
-- url     : https://prove2.me/theorems/c8812b28-e8ad-4cfb-ad24-fc1013c69b1a
-- title:
--   Global Theory: finite of is Integral Closure dedekind
-- statement:
--   The Global Theory construction uses the finite of is Integral Closure dedekind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L443-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L443-L448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable (o R : Type*) [CommRing o] [IsDedekindDomain o] [CommRing R] [Algebra o R]
  [Algebra.FiniteType o R]

theorem GlobalTheory.finite_of_isIntegralClosure_dedekind [CharZero o] [IsDomain R] [FaithfulSMul o R]
    (K L C : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [CommRing C] [Algebra R C]
    [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L] : Module.Finite R C := by sorry
