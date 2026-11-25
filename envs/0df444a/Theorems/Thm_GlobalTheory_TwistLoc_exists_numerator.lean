-- Prove2me | Theorems.Thm_GlobalTheory_TwistLoc_exists_numerator
-- name    : GlobalTheory.TwistLoc.exists_numerator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:17:17.911345+00:00
-- url     : https://prove2.me/theorems/b4c7e4c0-68e3-48ae-93c7-256cb9bf73eb
-- title:
--   Twist Loc: exists numerator
-- statement:
--   The Twist Loc construction uses the exists numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L135-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}}
variable {Rm : Type} [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
  {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
  (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
include H

theorem GlobalTheory.TwistLoc.exists_numerator {U : Y.Opens} (hU : IsAffineOpen U) (x : Γ(Y', h ⁻¹ᵁ U)) :
    ∃ t ∈ M, ∃ a : Γ(Y, U), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), h (r z) ∈ U →
      gs (r ≫ h) z U a = gc (r ≫ h ≫ π) z t * gs r z _ x := by sorry
