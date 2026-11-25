-- Prove2me | Theorems.Thm_GlobalTheory_SharpGradient_conj_diag
-- name    : GlobalTheory.SharpGradient.conj_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:41:01.236818+00:00
-- url     : https://prove2.me/theorems/83641e1c-08d8-4cb7-a727-303c77c0e48f
-- title:
--   Sharp Gradient: conj diag
-- statement:
--   The Sharp Gradient construction uses the conj diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L194-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L194-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate

theorem GlobalTheory.SharpGradient.conj_diag {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    (Z : Matrix (Fin p) (Fin q) ℂ) (a : Fin p) :
    ((Uᴴ * (1 - Z * Zᴴ) * U : Matrix (Fin p) (Fin p) ℂ) a a).re = 1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b) := by sorry
