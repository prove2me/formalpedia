-- Prove2me | Theorems.Thm_GlobalTheory_BK_Ehat_mem_nonZeroDivisors
-- name    : GlobalTheory.BK.Ehat_mem_nonZeroDivisors
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:57:59.83432+00:00
-- url     : https://prove2.me/theorems/f381d551-c408-4dc6-9438-7749d86a607a
-- title:
--   BK: Ehat mem non Zero Divisors
-- statement:
--   The BK construction uses the Ehat mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapMemNonZeroDivisorsAdicCompletion.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapMemNonZeroDivisorsAdicCompletion.lean#L26-L30

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

theorem GlobalTheory.BK.Ehat_mem_nonZeroDivisors (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by sorry
