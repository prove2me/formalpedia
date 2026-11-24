-- Prove2me | Theorems.Thm_GlobalTheory_ZM_appLE_spConst
-- name    : GlobalTheory.ZM.appLE_spConst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:00.917853+00:00
-- url     : https://prove2.me/theorems/357a007a-e5bb-4f5d-a305-0044b13ae891
-- title:
--   ZM: app LE sp Const
-- statement:
--   The ZM construction uses the app LE sp Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L50-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
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
noncomputable section
open GlobalTheory GlobalTheory.ZM

theorem GlobalTheory.ZM.appLE_spConst {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (W : (Sp R).Opens)
    (W' : (Sp R').Opens) (h : W' ≤ spMap φ ⁻¹ᵁ W) (r : R) :
    ((spMap φ).appLE W W' h).hom (spConst R W r) = spConst R' W' (φ r) := by sorry
