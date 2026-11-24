-- Prove2me | Theorems.Thm_GlobalTheory_PsiEvenPull_sym_pull
-- name    : GlobalTheory.PsiEvenPull.sym_pull
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:56:41.329872+00:00
-- url     : https://prove2.me/theorems/6e8979ee-1610-40c2-bde6-c0e724c90201
-- title:
--   Psi Even Pull: sym pull
-- statement:
--   The Psi Even Pull construction uses the sym pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L87-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L87-L122

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

theorem GlobalTheory.PsiEvenPull.sym_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ proj hD) z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := by sorry
