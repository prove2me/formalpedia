-- Prove2me | Theorems.Thm_GlobalTheory_BK_isAdicComplete_S
-- name    : GlobalTheory.BK.isAdicComplete_S
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:15.212664+00:00
-- url     : https://prove2.me/theorems/b1e01ed5-2cd7-4f60-b022-60dd2470011a
-- title:
--   BK: is Adic Complete S
-- statement:
--   The BK construction uses the is Adic Complete S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L95-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK

theorem GlobalTheory.BK.isAdicComplete_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : IsAdicComplete (Ideal.span {(l : S O K e)}) (S O K e) := by sorry
