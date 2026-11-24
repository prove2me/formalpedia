-- Prove2me | Theorems.Thm_GlobalTheory_PicPi_single_smul_eq_zero
-- name    : GlobalTheory.PicPi.single_smul_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:44:11.418188+00:00
-- url     : https://prove2.me/theorems/f72854f7-fc72-4dd3-999c-472e8b8d7e90
-- title:
--   Pic Pi: single smul eq zero
-- statement:
--   The Pic Pi construction uses the single smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicPiIsOfFinOrder.lean#L28-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicPiIsOfFinOrder.lean#L28-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.PicPi
variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]

theorem GlobalTheory.PicPi.single_smul_eq_zero (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i) (y : M)
    (h : (1 : R i) ⊗ₜ[(j : ι) → R j] y = 0) : (Pi.single i 1 : (j : ι) → R j) • y = 0 := by sorry
