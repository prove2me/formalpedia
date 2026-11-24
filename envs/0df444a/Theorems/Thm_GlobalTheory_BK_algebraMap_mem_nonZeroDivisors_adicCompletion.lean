-- Prove2me | Theorems.Thm_GlobalTheory_BK_algebraMap_mem_nonZeroDivisors_adicCompletion
-- name    : GlobalTheory.BK.algebraMap_mem_nonZeroDivisors_adicCompletion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:53.319016+00:00
-- url     : https://prove2.me/theorems/4991d1db-660f-4f7c-b580-1ba0388f2469
-- title:
--   BK: algebra Map mem non Zero Divisors adic Completion
-- statement:
--   The BK construction uses the algebra Map mem non Zero Divisors adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapMemNonZeroDivisorsAdicCompletion.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapMemNonZeroDivisorsAdicCompletion.lean#L8-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology

theorem GlobalTheory.BK.algebraMap_mem_nonZeroDivisors_adicCompletion {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by sorry
