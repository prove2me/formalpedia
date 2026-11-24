-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_fderiv_lift
-- name    : GlobalTheory.LocLift.fderiv_lift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:13:16.672845+00:00
-- url     : https://prove2.me/theorems/081eee52-7415-49c4-9499-8bc3056481ad
-- title:
--   Loc Lift: fderiv lift
-- statement:
--   The Loc Lift construction uses the fderiv lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivLift.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivLift.lean#L96-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]

theorem GlobalTheory.LocLift.fderiv_lift {x : V → Q} {e : W → Q} (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w)
    (hs : Function.Surjective e) {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) (z : V) : e (fderiv ℂ ζ 0 z) = x z := by sorry
