-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_genericFibre_of_smooth
-- name    : GlobalTheory.isIntegral_genericFibre_of_smooth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:51.193191+00:00
-- url     : https://prove2.me/theorems/3550f6eb-7768-4b9d-aefb-dcbfffff97af
-- title:
--   Global Theory: is Integral generic Fibre of smooth
-- statement:
--   The Global Theory construction uses the is Integral generic Fibre of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean#L202-L205

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
variable {X : Scheme.{u}} {V : Type u} [CommRing V]

theorem GlobalTheory.isIntegral_genericFibre_of_smooth [IsDomain V] (K : Type u) [Field K] [Algebra V K]
    [IsFractionRing V K] (f : X ⟶ Spec (.of V)) [Smooth f] [GeometricallyConnected f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) := by sorry
