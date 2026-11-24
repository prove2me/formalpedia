-- Prove2me | Theorems.Thm_GlobalTheory_NilProper_isProper_and_geometricallyConnected_of_isNilpotent
-- name    : GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:03.856936+00:00
-- url     : https://prove2.me/theorems/dc19f3f2-d968-418e-aeec-cfd9444a728d
-- title:
--   Nil Proper: is Proper and geometrically Connected of is Nilpotent
-- statement:
--   The Nil Proper construction uses the is Proper and geometrically Connected of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsProperAndGeometricallyConnectedOfIsNilpotent.lean#L47-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsProperAndGeometricallyConnectedOfIsNilpotent.lean#L47-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsProperAndGeometricallyConnectedOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilProper

theorem GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent :
    ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (Y : Over (Spec (CommRingCat.of A))) [LocallyOfFiniteType Y.hom], (IsProper (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → IsProper Y.hom) ∧ (GeometricallyConnected (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → GeometricallyConnected Y.hom) := by sorry
