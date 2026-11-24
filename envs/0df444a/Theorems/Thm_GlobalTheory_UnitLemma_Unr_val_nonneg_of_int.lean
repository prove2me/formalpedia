-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_nonneg_of_int
-- name    : GlobalTheory.UnitLemma.Unr.val_nonneg_of_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:06.324584+00:00
-- url     : https://prove2.me/theorems/6dd5766d-ee77-4238-8d28-e0d933acd679
-- title:
--   Unr: val nonneg of int
-- statement:
--   The Unr construction uses the val nonneg of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedInvolutionExtMapsIntegersToIntegers.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedInvolutionExtMapsIntegersToIntegers.lean#L17-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by sorry
