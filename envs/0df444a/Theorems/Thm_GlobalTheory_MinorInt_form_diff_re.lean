-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_form_diff_re
-- name    : GlobalTheory.MinorInt.form_diff_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:06.683798+00:00
-- url     : https://prove2.me/theorems/95bfd1a0-b375-4915-87fc-05d30f5f0b41
-- title:
--   Minor Int: form diff re
-- statement:
--   The Minor Int construction uses the form diff re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L103-L106

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

theorem GlobalTheory.MinorInt.form_diff_re {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ)
    (t : ι → ℂ) : (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re =
      ∑ k, ‖(A *ᵥ t) k‖ ^ 2 - ∑ k, ‖(C *ᵥ t) k‖ ^ 2 := by sorry
