-- Prove2me | Theorems.Thm_GlobalTheory_det_of_blockTriangular_injective
-- name    : GlobalTheory.det_of_blockTriangular_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:52.673615+00:00
-- url     : https://prove2.me/theorems/75f5392a-6546-4def-bdf1-153f07ec6e5f
-- title:
--   Global Theory: det of block Triangular injective
-- statement:
--   The Global Theory construction uses the det of block Triangular injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetOfBlockTriangularInjective.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetOfBlockTriangularInjective.lean#L8-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetOfBlockTriangularInjective
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
open GlobalTheory

theorem GlobalTheory.det_of_blockTriangular_injective {m α R : Type} [Fintype m] [DecidableEq m]
    [LinearOrder α] [CommRing R] (M : Matrix m m R) (f : m → α) (hf : Function.Injective f)
    (h : M.BlockTriangular f) : M.det = ∏ i, M i i := by sorry
