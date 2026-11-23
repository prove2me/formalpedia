-- Prove2me | Theorems.Thm_GlobalTheory_PsiInPull_res_toOpen
-- name    : GlobalTheory.PsiInPull.res_toOpen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:31.752879+00:00
-- url     : https://prove2.me/theorems/3eb7c5b2-7d4e-4c36-9c82-187e66b1cf90
-- title:
--   Psi In Pull: res to Open
-- statement:
--   The Psi In Pull construction uses the res to Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L45-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
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
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull

theorem GlobalTheory.PsiInPull.res_toOpen {R : Type} [CommRing R] {U V : (Spec (CommRingCat.of R)).Opens} (h : U ≤ V) (a : R) :
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE h).op).hom (DegPre.toOpen V a) = DegPre.toOpen U a := by sorry
