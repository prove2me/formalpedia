-- Prove2me | Theorems.Thm_GlobalTheory_HomExt_finite_preimage_of_finite_lifts
-- name    : GlobalTheory.HomExt.finite_preimage_of_finite_lifts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:00.022972+00:00
-- url     : https://prove2.me/theorems/8d94479f-6fea-4c85-8997-e9792a3ee349
-- title:
--   Hom Ext: finite preimage of finite lifts
-- statement:
--   The Hom Ext construction uses the finite preimage of finite lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfDensePartOfIsIntegral.lean#L42-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfDensePartOfIsIntegral.lean#L42-L56

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

theorem GlobalTheory.HomExt.finite_preimage_of_finite_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : (f ⁻¹' Set.range y).Finite := by sorry
