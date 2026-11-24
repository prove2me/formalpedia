-- Prove2me | Theorems.Thm_GlobalTheory_prod_lowerPairs_snd
-- name    : GlobalTheory.prod_lowerPairs_snd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:48.252137+00:00
-- url     : https://prove2.me/theorems/4645a26c-d1b1-477b-85ab-83feea4ee5ac
-- title:
--   Global Theory: prod lower Pairs snd
-- statement:
--   The Global Theory construction uses the prod lower Pairs snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetOfBlockTriangularInjective.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetOfBlockTriangularInjective.lean#L26-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetOfBlockTriangularInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory

theorem GlobalTheory.prod_lowerPairs_snd {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.2 = ∏ a, d a ^ (r - 1 - (a : ℕ)) := by sorry
