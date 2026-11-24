-- Prove2me | Theorems.Thm_GlobalTheory_PsiEvenPull_even_on
-- name    : GlobalTheory.PsiEvenPull.even_on
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:14.46141+00:00
-- url     : https://prove2.me/theorems/1c1b6f5c-904c-4815-a6d2-7feaa29e790e
-- title:
--   Psi Even Pull: even on
-- statement:
--   The Psi Even Pull construction uses the even on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L51-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L51-L75

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

theorem GlobalTheory.PsiEvenPull.even_on (h : D.PsiEven) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (χ : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (TW W).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val (ψW.psi (-χ)) r z J * val D.sym (r ≫ (toUnit (TW W) ≫ D.c χ).left) z J = val (ψW.psi χ) r z J := by sorry
