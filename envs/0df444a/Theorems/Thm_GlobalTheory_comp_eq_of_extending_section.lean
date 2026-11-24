-- Prove2me | Theorems.Thm_GlobalTheory_comp_eq_of_extending_section
-- name    : GlobalTheory.comp_eq_of_extending_section
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:52.891802+00:00
-- url     : https://prove2.me/theorems/d1816207-f7bc-48f1-9d1e-90157d67c763
-- title:
--   Global Theory: comp eq of extending section
-- statement:
--   The Global Theory construction uses the comp eq of extending section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionPointFixedOfGenericSectionsFixed.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionPointFixedOfGenericSectionsFixed.lean#L15-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointFixedOfGenericSectionsFixed
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.comp_eq_of_extending_section {X U W G T : Scheme.{0}} [IsReduced X] (j : U ⟶ X)
    [IsDominant j] (g : G ⟶ X) [IsSeparated g] (a : W ⟶ G) [IsOpenImmersion (a ≫ g)]
    (s : U ⟶ G) (hs : pullback.fst (a ≫ g) j ≫ a = pullback.snd (a ≫ g) j ≫ s)
    (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G ⟶ G) (hr : r₀ ≫ j = j ≫ r) (hφ : φ ≫ g = g ≫ r)
    (hsφ : s ≫ φ = r₀ ≫ s) (w : T ⟶ W) (hw : w ≫ (a ≫ g) ≫ r = w ≫ a ≫ g) :
    w ≫ a ≫ φ = w ≫ a := by sorry
