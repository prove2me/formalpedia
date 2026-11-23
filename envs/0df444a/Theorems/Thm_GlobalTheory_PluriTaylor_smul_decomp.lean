-- Prove2me | Theorems.Thm_GlobalTheory_PluriTaylor_smul_decomp
-- name    : GlobalTheory.PluriTaylor.smul_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:28.78309+00:00
-- url     : https://prove2.me/theorems/18431894-5b7e-452c-851c-216d4747b5b4
-- title:
--   Pluri Taylor: smul decomp
-- statement:
--   The Pluri Taylor construction uses the smul decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L13-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Complex Set
variable {n : ℕ}

theorem GlobalTheory.PluriTaylor.smul_decomp (c : ℂ) (v : V n) : c • v = c.re • v + c.im • (I • v) := by sorry
