-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_sum_powCoeff
-- name    : GroundTheory.PAdicHodge.ACris.sum_powCoeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:08.331194+00:00
-- url     : https://prove2.me/theorems/2cf4ba6d-20e9-5c6f-bf55-85bab68b0346
-- title:
--   ACris: sum pow Coeff
-- statement:
--   The ACris construction uses the sum pow Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L36-L45

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

theorem GroundTheory.PAdicHodge.ACris.sum_powCoeff (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1 : ℤ) ^ n * powCoeff q (n + 1) (j + 1) *
      (((j + 1).factorial / (n + 1) : ℕ) : ℤ) = (-1) ^ j * q * j.factorial := by sorry
