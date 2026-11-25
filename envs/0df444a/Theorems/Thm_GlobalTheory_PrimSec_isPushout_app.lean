-- Prove2me | Theorems.Thm_GlobalTheory_PrimSec_isPushout_app
-- name    : GlobalTheory.PrimSec.isPushout_app
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:57:35.380003+00:00
-- url     : https://prove2.me/theorems/1d40f2ae-abcb-4328-93f5-8d680deb0ec3
-- title:
--   Prim Sec: is Pushout app
-- statement:
--   The Prim Sec construction uses the is Pushout app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L18-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem GlobalTheory.PrimSec.isPushout_app {g : R →+* R'} {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (AbLaw.cst f U)) (CommRingCat.ofHom g) (π.app U)
      (CommRingCat.ofHom (AbLaw.cst f' (π ⁻¹ᵁ U))) := by sorry
