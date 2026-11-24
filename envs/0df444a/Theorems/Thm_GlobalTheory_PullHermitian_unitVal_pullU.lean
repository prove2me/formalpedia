-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_unitVal_pullU
-- name    : GlobalTheory.PullHermitian.unitVal_pullU
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:40.223569+00:00
-- url     : https://prove2.me/theorems/1d4b3b41-6656-4d54-83d2-9f5e3af6f15d
-- title:
--   Pull Hermitian: unit Val pull U
-- statement:
--   The Pull Hermitian construction uses the unit Val pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L31-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
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
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem GlobalTheory.PullHermitian.unitVal_pullU {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U))
    (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)ˣ) :
    unitVal x h (pullU φ U f) = unitVal (x ≫ φ) h' f := by sorry
