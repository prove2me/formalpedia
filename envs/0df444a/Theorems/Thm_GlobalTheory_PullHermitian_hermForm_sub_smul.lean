-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_hermForm_sub_smul
-- name    : GlobalTheory.PullHermitian.hermForm_sub_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:46.03985+00:00
-- url     : https://prove2.me/theorems/bb6f546f-6eb7-4f3e-afe5-06f907fc5712
-- title:
--   Pull Hermitian: herm Form sub smul
-- statement:
--   The Pull Hermitian construction uses the herm Form sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L153-L155

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

theorem GlobalTheory.PullHermitian.hermForm_sub_smul {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ) (a b : ℂ) (z w : Fin g → ℂ) :
    hermForm (a • H - b • H') z w = a * hermForm H z w - b * hermForm H' z w := by sorry
