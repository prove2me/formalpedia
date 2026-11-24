-- Prove2me | Theorems.Thm_GlobalTheory_SepIdem_formallyUnramified_of_isReduced
-- name    : GlobalTheory.SepIdem.formallyUnramified_of_isReduced
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:59.563961+00:00
-- url     : https://prove2.me/theorems/2b9b583d-9c72-4f8d-9626-cea44d787399
-- title:
--   Sep Idem: formally Unramified of is Reduced
-- statement:
--   The Sep Idem construction uses the formally Unramified of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormallyUnramifiedOfIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.SepIdem

theorem GlobalTheory.SepIdem.formallyUnramified_of_isReduced (K A : Type) [Field K] [PerfectField K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.FormallyUnramified K A := by sorry
