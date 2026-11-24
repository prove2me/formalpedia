-- Prove2me | Theorems.Thm_GlobalTheory_isDedekindDomain_integralClosure_of_dimensionLEOne
-- name    : GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:57.610235+00:00
-- url     : https://prove2.me/theorems/57c312f4-1331-4d0a-8c7e-3a0be6a45497
-- title:
--   Global Theory: is Dedekind Domain integral Closure of dimension LEOne
-- statement:
--   The Global Theory construction uses the is Dedekind Domain integral Closure of dimension LEOne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L549-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L549-L555

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  (K : Type*) {L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
include K

theorem GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne :
    IsDedekindDomain (integralClosure A L) := by sorry
