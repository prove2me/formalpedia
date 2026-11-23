-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_det_ne_zero_of_form
-- name    : GlobalTheory.MinorInt.det_ne_zero_of_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:46.410004+00:00
-- url     : https://prove2.me/theorems/d1bbd67c-eefa-4a12-8583-9b5e540b5bdb
-- title:
--   Minor Int: det ne zero of form
-- statement:
--   The Minor Int construction uses the det ne zero of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L108-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L108-L122

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

theorem GlobalTheory.MinorInt.det_ne_zero_of_form {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ)
    (h : ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re) :
    A.det ≠ 0 := by sorry
