-- Prove2me | Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth_of_geometricallyConnected
-- name    : GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:42.641382+00:00
-- url     : https://prove2.me/theorems/0839a2c7-574c-50f2-8355-60e1985828e0
-- title:
--   Global Theory: geometrically Integral of smooth of geometrically Connected
-- statement:
--   The Global Theory construction uses the geometrically Integral of smooth of geometrically Connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L249-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L249-L291

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected :
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f],
      GeometricallyIntegral f ∧ (IsIntegral S → IsIntegral X)) ∧
    (∀ {S : Scheme.{u}} (A : Over S) [GrpObj A], IsAbelianScheme A ∨ IsSemiAbelian A →
      ∀ T ∈ [A, G2 A, G3 A, G4 A],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left)) ∧
    (∀ {S : Scheme.{u}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom],
      ∀ T ∈ [G, G2 G, G3 G, G4 G],
        GeometricallyIntegral T.hom ∧ (IsIntegral S → IsIntegral T.left)) ∧
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
      [Smooth G.hom] [GeometricallyConnected G.hom], ∀ T ∈ [G, G2 G, G3 G, G4 G],
        IsIntegral T.left ∧ IsLocallyNoetherian T.left ∧
        IsIntegral (pullback T.hom (spMap (IsLocalRing.residue V))) ∧
        IsIntegral (pullback T.hom (spMap (algebraMap V (FractionRing V))))) := by sorry
