-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_surjective_specMap_field
-- name    : GlobalTheory.ComplexPoints.surjective_specMap_field
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:29.748772+00:00
-- url     : https://prove2.me/theorems/f3d5bab3-3fe2-4cbb-93f4-7f36963e982e
-- title:
--   Complex Points: surjective spec Map field
-- statement:
--   The Complex Points construction uses the surjective spec Map field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L42-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem GlobalTheory.ComplexPoints.surjective_specMap_field {k L : Type u} [Field k] [Field L] (σ : k →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) := by sorry
