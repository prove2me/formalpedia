-- Prove2me | Theorems.Thm_GlobalTheory_isFinite_fromNormalization_of_locallyOfFiniteType
-- name    : GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:55.679223+00:00
-- url     : https://prove2.me/theorems/ebd0f279-8698-4d59-9fff-abb709b111f9
-- title:
--   Global Theory: is Finite from Normalization of locally Of Finite Type
-- statement:
--   The Global Theory construction uses the is Finite from Normalization of locally Of Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L577-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L577-L582

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

theorem GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType [IsReduced X] [LocallyOfFiniteType f]
    (hchar : ∀ x ∈ genericPoints X, CharZero (X.residueField x)) :
    IsFinite f.fromNormalization := by sorry
