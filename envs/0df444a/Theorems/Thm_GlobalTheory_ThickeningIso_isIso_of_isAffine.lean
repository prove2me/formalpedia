-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningIso_isIso_of_isAffine
-- name    : GlobalTheory.ThickeningIso.isIso_of_isAffine
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:48.724941+00:00
-- url     : https://prove2.me/theorems/a79652a1-97f9-40b2-9be2-e3e6d63b5160
-- title:
--   Thickening Iso: is Iso of is Affine
-- statement:
--   The Thickening Iso construction uses the is Iso of is Affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEps.lean#L97-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEps.lean#L97-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.ThickeningIso

theorem GlobalTheory.ThickeningIso.isIso_of_isAffine {K : Type} [Field K] {Y Y' Z' : Scheme.{0}} [IsAffine Z'] {q : Y ⟶ Sp K}
    {π' : Z' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'} {e : Y' ⟶ Z'}
    (h : IsPullback j q (e ≫ π') (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (h' : IsPullback (j ≫ e) q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hf : Flat (e ≫ π')) : IsIso e := by sorry
