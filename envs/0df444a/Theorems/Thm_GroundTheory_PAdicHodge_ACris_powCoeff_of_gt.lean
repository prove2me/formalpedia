-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_powCoeff_of_gt
-- name    : GroundTheory.PAdicHodge.ACris.powCoeff_of_gt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:49.744802+00:00
-- url     : https://prove2.me/theorems/c3875747-4689-4477-a920-0dd6de62f627
-- title:
--   ACris: pow Coeff of gt
-- statement:
--   The ACris construction uses the pow Coeff of gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L33-L34

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

theorem GroundTheory.PAdicHodge.ACris.powCoeff_of_gt {N m : ℕ} (h : q * N < m) : powCoeff q N m = 0 := by sorry
