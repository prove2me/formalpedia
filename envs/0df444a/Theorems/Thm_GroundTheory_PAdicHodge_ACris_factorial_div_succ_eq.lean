-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_factorial_div_succ_eq
-- name    : GroundTheory.PAdicHodge.ACris.factorial_div_succ_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:46.529862+00:00
-- url     : https://prove2.me/theorems/a1cbac6c-046b-47b3-8317-9ade4be8e869
-- title:
--   ACris: factorial div succ eq
-- statement:
--   The ACris construction uses the factorial div succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L47-L51

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

theorem GroundTheory.PAdicHodge.ACris.factorial_div_succ_eq {n j : ℕ} (h : n ≤ j) :
    (j + 1).factorial / (n + 1) = n.factorial * ((j + 1).factorial / (n + 1).factorial) := by sorry
