-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaWeightedNorm_ThetaIn_constant_lt_t_mul_a
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn.constant_lt_t_mul_a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:16.001345+00:00
-- url     : https://prove2.me/theorems/1e8ae254-9ce6-50d7-a25f-dfcfa386f014
-- title:
--   Theta In: constant lt t mul a
-- statement:
--   The Theta In construction uses the constant lt t mul a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaWeightedNorm.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaWeightedNorm.lean#L188-L193

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaWeightedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn
variable {X : Data E r} (I : ThetaIn X)

theorem GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn.constant_lt_t_mul_a : I.c1 < I.t * I.a1 := by sorry
