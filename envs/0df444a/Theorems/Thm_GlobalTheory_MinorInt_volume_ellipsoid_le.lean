-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_volume_ellipsoid_le
-- name    : GlobalTheory.MinorInt.volume_ellipsoid_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:09.388832+00:00
-- url     : https://prove2.me/theorems/a3664389-837b-48e3-9e6d-762a55c04b3e
-- title:
--   Minor Int: volume ellipsoid le
-- statement:
--   The Minor Int construction uses the volume ellipsoid le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L18-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.volume_ellipsoid_le {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℝ) {H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (hd : H.det ≠ 0) :
    volume {x : ι → ℂ | (star x ⬝ᵥ H *ᵥ x).re ≤ R} ≤
      ENNReal.ofReal ‖H.det‖⁻¹ * volume (Metric.closedBall (0 : ι → ℂ) (Real.sqrt R)) := by sorry
