-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_form_gram_re
-- name    : GlobalTheory.MinorInt.form_gram_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:21.039535+00:00
-- url     : https://prove2.me/theorems/0da26a52-bc03-4d39-8fd7-50632b3d6a10
-- title:
--   Minor Int: form gram re
-- statement:
--   The Minor Int construction uses the form gram re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L14-L16

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

theorem GlobalTheory.MinorInt.form_gram_re {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix κ ι ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ (Bᴴ * B) *ᵥ x).re = ∑ k, ‖(B *ᵥ x) k‖ ^ 2 := by sorry
