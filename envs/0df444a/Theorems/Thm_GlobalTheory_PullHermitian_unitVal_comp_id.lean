-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_unitVal_comp_id
-- name    : GlobalTheory.PullHermitian.unitVal_comp_id
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:33.471851+00:00
-- url     : https://prove2.me/theorems/94efa152-99e9-4947-8e79-b98965f5e020
-- title:
--   Pull Hermitian: unit Val comp id
-- statement:
--   The Pull Hermitian construction uses the unit Val comp id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L40-L42

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

theorem GlobalTheory.PullHermitian.unitVal_comp_id {U : X.Opens} (h : ⊤ ≤ (x ≫ 𝟙 X) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    unitVal (x ≫ 𝟙 X) h f = unitVal x h' f := by sorry
