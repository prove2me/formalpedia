-- Prove2me | Theorems.Thm_GlobalTheory_HomExt_isIso_of_densePart_of_isIntegral
-- name    : GlobalTheory.HomExt.isIso_of_densePart_of_isIntegral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:23.847403+00:00
-- url     : https://prove2.me/theorems/bbe673de-c548-4388-8026-8e28a1e14506
-- title:
--   Hom Ext: is Iso of dense Part of is Integral
-- statement:
--   The Hom Ext construction uses the is Iso of dense Part of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfDensePartOfIsIntegral.lean#L58-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfDensePartOfIsIntegral.lean#L58-L85

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

theorem GlobalTheory.HomExt.isIso_of_densePart_of_isIntegral {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsIntegral Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by sorry
