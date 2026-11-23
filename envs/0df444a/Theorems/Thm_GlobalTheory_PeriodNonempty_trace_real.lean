-- Prove2me | Theorems.Thm_GlobalTheory_PeriodNonempty_trace_real
-- name    : GlobalTheory.PeriodNonempty.trace_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:17.18594+00:00
-- url     : https://prove2.me/theorems/64fb2235-cdfc-4ee6-8672-554c8f61f0ba
-- title:
--   Period Nonempty: trace real
-- statement:
--   The Period Nonempty construction uses the trace real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L72-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section

theorem GlobalTheory.PeriodNonempty.trace_real {W : Type} [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) :
    LinearMap.trace ℝ W (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ W f).re := by sorry
