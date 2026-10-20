-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicInterpolation_cartanCharacteristicInterpolationProjector_apply_of_eigenvector
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation.cartanCharacteristicInterpolationProjector_apply_of_eigenvector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/3dc808ec-7a80-48f4-ab69-d5a16265af66
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation.cartanCharacteristicInterpolationProjector_apply_of_eigenvector
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation.cartanCharacteristicInterpolationProjector_apply_of_eigenvector
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (nodes : ι → ℝ) (T : Module.End ℝ V)
    (hnode : Function.Injective nodes)
    (i j : ι) (x : V) (hx : T x = nodes j • x) :
    cartanCharacteristicInterpolationProjector nodes T i x =
      if i = j then x else 0 := by sorry
