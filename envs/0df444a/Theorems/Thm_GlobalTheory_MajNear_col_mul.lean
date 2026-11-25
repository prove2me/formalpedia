-- Prove2me | Theorems.Thm_GlobalTheory_MajNear_col_mul
-- name    : GlobalTheory.MajNear.col_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:34:15.871402+00:00
-- url     : https://prove2.me/theorems/c978e02f-5326-4ab1-ba9f-93d9ebeb58ca
-- title:
--   Maj Near: col mul
-- statement:
--   The Maj Near construction uses the col mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L43-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsomOfGramEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_col_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MajNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MajNear.col_mul {r : ℕ} (g M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * M) a = g *ᵥ col M a := by sorry
