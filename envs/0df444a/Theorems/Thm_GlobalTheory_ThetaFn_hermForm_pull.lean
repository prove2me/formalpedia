-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_hermForm_pull
-- name    : GlobalTheory.ThetaFn.hermForm_pull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:11.65472+00:00
-- url     : https://prove2.me/theorems/004d236d-b0d7-4177-bf03-8983bee357b0
-- title:
--   Theta Fn: herm Form pull
-- statement:
--   The Theta Fn construction uses the herm Form pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L16-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter

theorem GlobalTheory.ThetaFn.hermForm_pull {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (z w : Fin g → ℂ) :
    hermForm ((LinearMap.toMatrix' Φ).transpose * Hm *
      (LinearMap.toMatrix' Φ).transpose.conjTranspose) z w = hermForm Hm (Φ z) (Φ w) := by sorry
