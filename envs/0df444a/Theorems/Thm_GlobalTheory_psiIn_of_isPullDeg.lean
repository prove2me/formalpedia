-- Prove2me | Theorems.Thm_GlobalTheory_psiIn_of_isPullDeg
-- name    : GlobalTheory.psiIn_of_isPullDeg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:15.379629+00:00
-- url     : https://prove2.me/theorems/71480781-de1d-4736-8750-f61ce0b2d23b
-- title:
--   Global Theory: psi In of is Pull Deg
-- statement:
--   The Global Theory construction uses the psi In of is Pull Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L167-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L167-L240

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
open PsiInPull

theorem GlobalTheory.psiIn_of_isPullDeg (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (x : D'.X) (J : Ideal R) (J' : Ideal R')
    (hJ : J.map φ ≤ J') (H : D.PsiIn (hD.xe x) J) : D'.PsiIn x J' := by sorry
