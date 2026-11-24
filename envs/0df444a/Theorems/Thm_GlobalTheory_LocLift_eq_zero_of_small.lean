-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_eq_zero_of_small
-- name    : GlobalTheory.LocLift.eq_zero_of_small
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:13:11.171979+00:00
-- url     : https://prove2.me/theorems/d22b4dcf-c28e-4925-af7b-36e1c3344f43
-- title:
--   Loc Lift: eq zero of small
-- statement:
--   The Loc Lift construction uses the eq zero of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivLift.lean#L125-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivLift.lean#L125-L135

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

theorem GlobalTheory.LocLift.eq_zero_of_small {T : Type} [TopologicalSpace T] {B : Set T} (hB : IsPreconnected B) {d : T → W}
    (hd : ContinuousOn d B) {r : ℝ} (hr : 0 < r) (h : ∀ b ∈ B, ‖d b‖ < r → d b = 0) {b₀ : T} (hb₀ : b₀ ∈ B)
    (h0 : d b₀ = 0) : ∀ b ∈ B, d b = 0 := by sorry
