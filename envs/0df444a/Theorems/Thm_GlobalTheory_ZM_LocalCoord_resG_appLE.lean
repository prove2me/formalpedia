-- Prove2me | Theorems.Thm_GlobalTheory_ZM_LocalCoord_resG_appLE
-- name    : GlobalTheory.ZM.LocalCoord.resG_appLE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:43.633441+00:00
-- url     : https://prove2.me/theorems/0804098d-9913-4d7d-85ed-b4790ccae75d
-- title:
--   Local Coord: res G app LE
-- statement:
--   The Local Coord construction uses the res G app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SectionCoordinateVectorExistsLocally.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SectionCoordinateVectorExistsLocally.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocally
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.LocalCoord

theorem GlobalTheory.ZM.LocalCoord.resG_appLE {X Y : Scheme.{0}} (x : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(X, U)) : resG Y hV ((x.appLE U V h).hom a) = (x.appLE U V' (hV.trans h)).hom a := by sorry
