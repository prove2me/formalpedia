-- Prove2me | Theorems.Thm_GlobalTheory_TwistLoc_isLocalization_app
-- name    : GlobalTheory.TwistLoc.isLocalization_app
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:05.144303+00:00
-- url     : https://prove2.me/theorems/8bdcf7ab-5d6d-5de4-817c-2fc804a0a1ef
-- title:
--   Twist Loc: is Localization app
-- statement:
--   The Twist Loc construction uses the is Localization app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L111-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L111-L133

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

theorem GlobalTheory.TwistLoc.isLocalization_app {U : Y.Opens} (hU : IsCompact (U : Set Y)) (hU' : IsQuasiSeparated (U : Set Y)) :
    letI := (h.app U).hom.toAlgebra
    IsLocalization (M.map (cst π U).hom) Γ(Y', h ⁻¹ᵁ U) := by sorry
