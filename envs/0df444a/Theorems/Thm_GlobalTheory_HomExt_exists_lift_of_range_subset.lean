-- Prove2me | Theorems.Thm_GlobalTheory_HomExt_exists_lift_of_range_subset
-- name    : GlobalTheory.HomExt.exists_lift_of_range_subset
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:04.234062+00:00
-- url     : https://prove2.me/theorems/f60d6f7f-b826-5718-b6f7-b06b479107eb
-- title:
--   Hom Ext: exists lift of range subset
-- statement:
--   The Hom Ext construction uses the exists lift of range subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfDensePartOfIsIntegral.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfDensePartOfIsIntegral.lean#L12-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfDensePartOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.HomExt

theorem GlobalTheory.HomExt.exists_lift_of_range_subset {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (x : T ⟶ X) (h : Set.range x ⊆ Set.range j) : ∃ y : T ⟶ U, y ≫ j = x := by sorry
