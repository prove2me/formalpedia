-- Prove2me | Theorems.Thm_GlobalTheory_geometricallyIntegral_of_isSemiAbelian
-- name    : GlobalTheory.geometricallyIntegral_of_isSemiAbelian
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:27:55.372516+00:00
-- url     : https://prove2.me/theorems/3bd1e4d3-7613-4cfb-88f6-7b1afcc143a6
-- title:
--   Global Theory: geometrically Integral of is Semi Abelian
-- statement:
--   The Global Theory construction uses the geometrically Integral of is Semi Abelian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L223-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L223-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{u}}

theorem GlobalTheory.geometricallyIntegral_of_isSemiAbelian (G : Over S) [GrpObj G] [h : IsSemiAbelian G] :
    GeometricallyIntegral G.hom := by sorry
