-- Prove2me | Theorems.Thm_GlobalTheory_PsiEvenPull_psi_pull
-- name    : GlobalTheory.PsiEvenPull.psi_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:25.212287+00:00
-- url     : https://prove2.me/theorems/c1b4abec-60d9-4e73-b7cb-feb65e4c87bb
-- title:
--   Psi Even Pull: psi pull
-- statement:
--   The Psi Even Pull construction uses the psi pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L124-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L124-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PsiEvenPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem GlobalTheory.PsiEvenPull.psi_pull (hD : IsPullDeg φ D D') (x : D'.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R').left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (hD.psiW.psi (hD.xe x)) (r ≫ hD.g) z J =
      (gw hD.w (r ≫ D'.xK x) z (J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))⁻¹ * val (D'.psi x) r z J' := by sorry
