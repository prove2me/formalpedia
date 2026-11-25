-- Prove2me | Theorems.Thm_GlobalTheory_MajNear_continuous_cpt
-- name    : GlobalTheory.MajNear.continuous_cpt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:47:43.235805+00:00
-- url     : https://prove2.me/theorems/f6bb52ca-464a-5f18-82a4-33401dc925b2
-- title:
--   Maj Near: continuous cpt
-- statement:
--   The Maj Near construction uses the continuous cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L65-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsomOfGramEq
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

theorem GlobalTheory.MajNear.continuous_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) := by sorry
