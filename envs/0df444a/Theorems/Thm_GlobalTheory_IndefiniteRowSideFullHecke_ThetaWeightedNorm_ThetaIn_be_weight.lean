-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaWeightedNorm_ThetaIn_be_weight
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn.be_weight
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:46.408445+00:00
-- url     : https://prove2.me/theorems/e6400e42-1d10-54d3-909f-011cdebae4bb
-- title:
--   Theta In: be weight
-- statement:
--   The Theta In construction uses the be weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaWeightedNorm.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaWeightedNorm.lean#L184-L186

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn.be_weight : 2 • ((I.i * I.g0h) • I.de2) + I.n1 • (2 • I.L - I.de2) = (2 * I.n1) • I.L := by sorry
