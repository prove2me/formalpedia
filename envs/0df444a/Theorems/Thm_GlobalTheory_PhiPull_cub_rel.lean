-- Prove2me | Theorems.Thm_GlobalTheory_PhiPull_cub_rel
-- name    : GlobalTheory.PhiPull.cub_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:03.485852+00:00
-- url     : https://prove2.me/theorems/9772cfaa-384d-4f0c-b5da-64d8d2116575
-- title:
--   Phi Pull: cub rel
-- statement:
--   The Phi Pull construction uses the cub rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L67-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L67-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem GlobalTheory.PhiPull.cub_rel (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {T' : Over (Spec (CommRingCat.of R'))} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' x.left))
    (a b c : T' ⟶ D'.P.A) :
    @Eq (T'.left.presheaf.stalk z)ˣ (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' a)
      (pushHom (pull_grp hD) T' b) (pushHom (pull_grp hD) T' c))
      (Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' z J' a b c) := by sorry
