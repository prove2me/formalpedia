-- Prove2me | Theorems.Thm_GlobalTheory_geometricallyConnected_fourthPower_hom
-- name    : GlobalTheory.geometricallyConnected_fourthPower_hom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:53.493416+00:00
-- url     : https://prove2.me/theorems/06bb9841-3486-4b91-833f-33b64bcb2c9b
-- title:
--   Global Theory: geometrically Connected fourth Power hom
-- statement:
--   The Global Theory construction uses the geometrically Connected fourth Power hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L138-L141

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
variable {S : Scheme.{u}}
open ReciprocityTheory.ChartRestriction.G.Semi
variable (G : Over S) [Smooth G.hom]
variable [GeometricallyConnected G.hom]

theorem GlobalTheory.geometricallyConnected_fourthPower_hom : GeometricallyConnected (G4 G).hom := by sorry
