-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_hermForm_pull
-- name    : GlobalTheory.PullHermitian.hermForm_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:57.882409+00:00
-- url     : https://prove2.me/theorems/ca2fc724-1f8a-4904-a99f-7f945a19608f
-- title:
--   Pull Hermitian: herm Form pull
-- statement:
--   The Pull Hermitian construction uses the herm Form pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L143-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L143-L151

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

theorem GlobalTheory.PullHermitian.hermForm_pull {g g' : ℕ} (H : Matrix (Fin g') (Fin g') ℂ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (z w : Fin g → ℂ) :
    hermForm ((LinearMap.toMatrix' F).transpose * H * (LinearMap.toMatrix' F).transpose.conjTranspose) z w =
      hermForm H (F z) (F w) := by sorry
