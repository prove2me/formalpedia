-- Prove2me | Theorems.Thm_GlobalTheory_DetClass_det_swap
-- name    : GlobalTheory.DetClass.det_swap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:02.37212+00:00
-- url     : https://prove2.me/theorems/62d8ae65-5fc6-4384-9611-0d0575c97ad0
-- title:
--   Det Class: det swap
-- statement:
--   The Det Class construction uses the det swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean#L21-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.DetClass.det_swap {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a b : (i : ι) → I i) :
    (∏ i, (b i : R)) * (mat φ a).det = (∏ i, (a i : R)) * (mat φ b).det := by sorry
