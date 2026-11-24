-- Prove2me | Theorems.Thm_GlobalTheory_PsiInPull_app_toOpen
-- name    : GlobalTheory.PsiInPull.app_toOpen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:14.496742+00:00
-- url     : https://prove2.me/theorems/a19edc6f-90ff-4963-a799-4aedeb6db3fa
-- title:
--   Psi In Pull: app to Open
-- statement:
--   The Psi In Pull construction uses the app to Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L51-L61

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

theorem GlobalTheory.PsiInPull.app_toOpen {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (V : (Spec (CommRingCat.of R)).Opens) (a : R) :
    ((specOf φ).app V).hom (DegPre.toOpen V a) = DegPre.toOpen (specOf φ ⁻¹ᵁ V) (φ a) := by sorry
