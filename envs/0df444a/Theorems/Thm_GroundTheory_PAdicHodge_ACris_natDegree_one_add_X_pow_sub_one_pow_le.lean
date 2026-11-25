-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_natDegree_one_add_X_pow_sub_one_pow_le
-- name    : GroundTheory.PAdicHodge.ACris.natDegree_one_add_X_pow_sub_one_pow_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:25.163927+00:00
-- url     : https://prove2.me/theorems/48a9042e-c684-50c2-b488-3f6f678f5f73
-- title:
--   ACris: nat Degree one add X pow sub one pow le
-- statement:
--   The ACris construction uses the nat Degree one add X pow sub one pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L20-L28

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

theorem GroundTheory.PAdicHodge.ACris.natDegree_one_add_X_pow_sub_one_pow_le (N : ℕ) :
    ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).natDegree ≤ q * N := by sorry
