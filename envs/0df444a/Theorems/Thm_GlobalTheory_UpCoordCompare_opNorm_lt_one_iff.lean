-- Prove2me | Theorems.Thm_GlobalTheory_UpCoordCompare_opNorm_lt_one_iff
-- name    : GlobalTheory.UpCoordCompare.opNorm_lt_one_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:27:31.426654+00:00
-- url     : https://prove2.me/theorems/0f1bf994-f21b-4da4-a887-61a219d73ca5
-- title:
--   Up Coord Compare: op Norm lt one iff
-- statement:
--   The Up Coord Compare construction uses the op Norm lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeadingBlockLowerEntriesToBlockCoords.lean#L67-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeadingBlockLowerEntriesToBlockCoords.lean#L67-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpCoordCompare
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff
noncomputable section

theorem GlobalTheory.UpCoordCompare.opNorm_lt_one_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Z : Matrix m n ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ < 1 ↔ (1 - Zᴴ * Z).PosDef := by sorry
