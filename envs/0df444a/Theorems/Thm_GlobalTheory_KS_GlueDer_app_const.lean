-- Prove2me | Theorems.Thm_GlobalTheory_KS_GlueDer_app_const
-- name    : GlobalTheory.KS.GlueDer.app_const
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:44:24.063798+00:00
-- url     : https://prove2.me/theorems/87d1f43e-3785-4a53-a4ce-2c4f6bf5d158
-- title:
--   Glue Der: app const
-- statement:
--   The Glue Der construction uses the app const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlobalLocDerOfIsCob.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlobalLocDerOfIsCob.lean#L35-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlobalLocDerOfIsCob
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.GlueDer

theorem GlobalTheory.KS.GlueDer.app_const {R K : Type} [CommRing R] [CommRing K] {X Y : Scheme.{0}} (x₀ : R →+* K) (p : X ⟶ Sp R)
    (q : Y ⟶ Sp K) (m : Y ⟶ X) (hm : m ≫ p = q ≫ spMap x₀) (U : X.Opens) (a : R) :
    (m.app U).hom (constFn p U a) = constFn q (m ⁻¹ᵁ U) (x₀ a) := by sorry
