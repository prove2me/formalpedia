-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDedekind_finrank_kaehler_eq_of_formallyUnramified
-- name    : GlobalTheory.SmoothDedekind.finrank_kaehler_eq_of_formallyUnramified
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:44.991032+00:00
-- url     : https://prove2.me/theorems/bbf72bd6-1cdc-4c60-a762-f969bd2ba949
-- title:
--   Smooth Dedekind: finrank kaehler eq of formally Unramified
-- statement:
--   The Smooth Dedekind construction uses the finrank kaehler eq of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L85-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing

theorem GlobalTheory.SmoothDedekind.finrank_kaehler_eq_of_formallyUnramified (R V L : Type*) [CommRing R] [CommRing V]
    [CommRing L] [Algebra R V] [Algebra V L] [Algebra R L] [IsScalarTower R V L]
    [Algebra.FormallyUnramified R V] :
    Module.finrank L Ω[L⁄R] = Module.finrank L Ω[L⁄V] := by sorry
