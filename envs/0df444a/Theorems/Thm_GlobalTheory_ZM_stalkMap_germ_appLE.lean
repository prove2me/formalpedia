-- Prove2me | Theorems.Thm_GlobalTheory_ZM_stalkMap_germ_appLE
-- name    : GlobalTheory.ZM.stalkMap_germ_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:37.413955+00:00
-- url     : https://prove2.me/theorems/6041c086-64ee-42d5-90b0-6b4f9abb0ae2
-- title:
--   ZM: stalk Map germ app LE
-- statement:
--   The ZM construction uses the stalk Map germ app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L16-L23

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

theorem GlobalTheory.ZM.stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : W' ≤ f ⁻¹ᵁ W)
    (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by sorry
