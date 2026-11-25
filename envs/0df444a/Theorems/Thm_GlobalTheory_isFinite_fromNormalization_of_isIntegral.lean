-- Prove2me | Theorems.Thm_GlobalTheory_isFinite_fromNormalization_of_isIntegral
-- name    : GlobalTheory.isFinite_fromNormalization_of_isIntegral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:30.096927+00:00
-- url     : https://prove2.me/theorems/8dc4a4d5-d0a3-4d81-94b4-e554f3515122
-- title:
--   Global Theory: is Finite from Normalization of is Integral
-- statement:
--   The Global Theory construction uses the is Finite from Normalization of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L601-L611
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L601-L611

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {o : CommRingCat.{u}} [IsDedekindDomain o]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o) [LocallyOfFiniteType g]
include g

theorem GlobalTheory.isFinite_fromNormalization_of_isIntegral [IsIntegral X] [CharZero X.functionField]
    (hess : (f.stalkMap (genericPoint X)).hom.EssFiniteType) : IsFinite f.fromNormalization := by sorry
