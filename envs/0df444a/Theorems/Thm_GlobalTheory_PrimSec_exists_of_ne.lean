-- Prove2me | Theorems.Thm_GlobalTheory_PrimSec_exists_of_ne
-- name    : GlobalTheory.PrimSec.exists_of_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:48.379036+00:00
-- url     : https://prove2.me/theorems/d73691a3-74ae-544a-ab46-6c307c64491d
-- title:
--   Prim Sec: exists of ne
-- statement:
--   The Prim Sec construction uses the exists of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L266-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L266-L283

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
variable {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K))) {M : LB X} (σ : LB.Sec (M.pull j))
include H

theorem GlobalTheory.PrimSec.exists_of_ne [Ring.DimensionLEOne O] (c : K) (i : M.ι) {x : X} (hx : x ∈ M.U i)
    (hfx : f x ≠ IsLocalRing.closedPoint O) :
    ∃ (V : X.Opens) (hV : V ≤ M.U i) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) c * loc σ i hV := by sorry
