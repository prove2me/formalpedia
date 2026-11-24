-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_blockDiagonal_mulVec
-- name    : GlobalTheory.UnitriJac.blockDiagonal_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:24.234392+00:00
-- url     : https://prove2.me/theorems/7a6eae21-7dfe-49bf-b7dc-f2507773a851
-- title:
--   Unitri Jac: block Diagonal mul Vec
-- statement:
--   The Unitri Jac construction uses the block Diagonal mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L205-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
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
open GlobalTheory GlobalTheory.UnitriJac
open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitriJac.blockDiagonal_mulVec {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
    (A : o → Matrix m m ℂ) (u : m × o → ℂ) (p : m) (τ : o) :
    (Matrix.blockDiagonal A *ᵥ u) (p, τ) = (A τ *ᵥ fun q => u (q, τ)) p := by sorry
