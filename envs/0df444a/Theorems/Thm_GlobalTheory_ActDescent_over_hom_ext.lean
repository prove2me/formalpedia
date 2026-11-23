-- Prove2me | Theorems.Thm_GlobalTheory_ActDescent_over_hom_ext
-- name    : GlobalTheory.ActDescent.over_hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:47.94611+00:00
-- url     : https://prove2.me/theorems/fa265c48-8b36-49f6-8047-0cc49ef50efe
-- title:
--   Act Descent: over hom ext
-- statement:
--   The Act Descent construction uses the over hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/OActDescendOfGenerators.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/OActDescendOfGenerators.lean#L22-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OActDescendOfGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ActDescent
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]

theorem GlobalTheory.ActDescent.over_hom_ext {X Y : Over S} {X' : Scheme.{0}} {φ : X' ⟶ X.left} {p : X' ⟶ U}
    (h : IsPullback φ p X.hom j) {f g : X ⟶ Y} (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by sorry
