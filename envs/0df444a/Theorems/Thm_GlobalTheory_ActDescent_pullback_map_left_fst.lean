-- Prove2me | Theorems.Thm_GlobalTheory_ActDescent_pullback_map_left_fst
-- name    : GlobalTheory.ActDescent.pullback_map_left_fst
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:47.124497+00:00
-- url     : https://prove2.me/theorems/c54030e4-1bf7-4885-8e79-8327dd990094
-- title:
--   Act Descent: pullback map left fst
-- statement:
--   The Act Descent construction uses the pullback map left fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/OActDescendOfGenerators.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/OActDescendOfGenerators.lean#L33-L35

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
omit [Flat j] [Surjective j]

theorem GlobalTheory.ActDescent.pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left := by sorry
