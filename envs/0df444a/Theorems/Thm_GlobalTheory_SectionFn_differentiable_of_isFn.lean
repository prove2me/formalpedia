-- Prove2me | Theorems.Thm_GlobalTheory_SectionFn_differentiable_of_isFn
-- name    : GlobalTheory.SectionFn.differentiable_of_isFn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:44.152621+00:00
-- url     : https://prove2.me/theorems/c0bbbdf0-5b03-43e0-bda6-22e04243b8d3
-- title:
--   Section Fn: differentiable of is Fn
-- statement:
--   The Section Fn construction uses the differentiable of is Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsThetaFnAndNeZeroOfIsFn.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsThetaFnAndNeZeroOfIsFn.lean#L16-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsThetaFnAndNeZeroOfIsFn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SectionFn
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem GlobalTheory.SectionFn.differentiable_of_isFn (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) :
    Differentiable ℂ θ := by sorry
