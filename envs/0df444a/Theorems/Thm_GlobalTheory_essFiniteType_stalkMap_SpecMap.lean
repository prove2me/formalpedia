-- Prove2me | Theorems.Thm_GlobalTheory_essFiniteType_stalkMap_SpecMap
-- name    : GlobalTheory.essFiniteType_stalkMap_SpecMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:54.472293+00:00
-- url     : https://prove2.me/theorems/16d247f7-d459-5db0-b803-3e1709fad130
-- title:
--   Global Theory: ess Finite Type stalk Map Spec Map
-- statement:
--   The Global Theory construction uses the ess Finite Type stalk Map Spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L500-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L500-L512

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

theorem GlobalTheory.essFiniteType_stalkMap_SpecMap {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.EssFiniteType) (x : Spec B) : ((Spec.map φ).stalkMap x).hom.EssFiniteType := by sorry
