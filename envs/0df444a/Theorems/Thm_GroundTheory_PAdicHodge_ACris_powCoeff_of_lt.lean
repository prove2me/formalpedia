-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_powCoeff_of_lt
-- name    : GroundTheory.PAdicHodge.ACris.powCoeff_of_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:20.273592+00:00
-- url     : https://prove2.me/theorems/941ec182-05b0-46f6-af6e-6389b5b9d320
-- title:
--   ACris: pow Coeff of lt
-- statement:
--   The ACris construction uses the pow Coeff of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L30-L31

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable (q : ℕ)

theorem GroundTheory.PAdicHodge.ACris.powCoeff_of_lt {N m : ℕ} (h : m < N) : powCoeff q N m = 0 := by sorry
