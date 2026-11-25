-- Prove2me | Theorems.Thm_GlobalTheory_PsiInPull_exists_of_locally
-- name    : GlobalTheory.PsiInPull.exists_of_locally
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:29.691051+00:00
-- url     : https://prove2.me/theorems/d7b515c9-88b1-4030-948e-8f7869b69f4e
-- title:
--   Psi In Pull: exists of locally
-- statement:
--   The Psi In Pull construction uses the exists of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L63-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L63-L112

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

theorem GlobalTheory.PsiInPull.exists_of_locally {R : Type} [CommRing R] [IsDomain R] (J : Ideal R)
    (z : Spec (CommRingCat.of (FractionRing R))) (t : (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V) (hz : jK R z ∈ V)
    (H : ∀ v ∈ V, ∃ U : (Spec (CommRingCat.of R)).Opens, U ≤ V ∧ v ∈ U ∧
      ∃ s ∈ J.map (DegPre.toOpen U), gs (jK R) z U s = t) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r = t := by sorry
