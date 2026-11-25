-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_aeval_mul_mem_of_stable
-- name    : GlobalTheory.UnitLemma.aeval_mul_mem_of_stable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:05:44.480229+00:00
-- url     : https://prove2.me/theorems/baa8b303-ac6b-4b2c-8261-30a336465f85
-- title:
--   Unit Lemma: aeval mul mem of stable
-- statement:
--   The Unit Lemma construction uses the aeval mul mem of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitOrbitsStableLatticesSeparable.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitOrbitsStableLatticesSeparable.lean#L13-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitOrbitsStableLatticesSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.aeval_mul_mem_of_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {g : A} {M : Submodule O A}
    (hM : ∀ y ∈ M, g * y ∈ M) (p : O[X]) {m : A} (hm : m ∈ M) : aeval g p * m ∈ M := by sorry
