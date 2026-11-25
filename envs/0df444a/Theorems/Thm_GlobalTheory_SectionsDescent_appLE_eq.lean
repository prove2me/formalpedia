-- Prove2me | Theorems.Thm_GlobalTheory_SectionsDescent_appLE_eq
-- name    : GlobalTheory.SectionsDescent.appLE_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:34.117208+00:00
-- url     : https://prove2.me/theorems/09668218-f213-5359-9a91-2aa35dfd2c34
-- title:
--   Sections Descent: app LE eq
-- statement:
--   The Sections Descent construction uses the app LE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L38-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
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
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange

theorem GlobalTheory.SectionsDescent.appLE_eq {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    (φ.appLE U V h).hom x = rs h ((φ.app U).hom x) := by sorry
