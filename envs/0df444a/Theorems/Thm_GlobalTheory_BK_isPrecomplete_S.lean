-- Prove2me | Theorems.Thm_GlobalTheory_BK_isPrecomplete_S
-- name    : GlobalTheory.BK.isPrecomplete_S
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:16.042347+00:00
-- url     : https://prove2.me/theorems/df0c07c5-c4ca-45a5-af42-e640aaed78e4
-- title:
--   BK: is Precomplete S
-- statement:
--   The BK construction uses the is Precomplete S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L54-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L54-L89

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem GlobalTheory.BK.isPrecomplete_S [CompleteSpace K] :
    IsPrecomplete (Ideal.span {(l : S O K e)}) (S O K e) := by sorry
