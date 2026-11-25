-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_le_max_of_le
-- name    : GroundTheory.PAdicHodge.norm_sub_le_max_of_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:18.968229+00:00
-- url     : https://prove2.me/theorems/03028913-2149-4cb8-8a2a-0fd115601827
-- title:
--   PAdic Hodge: norm sub le max of le
-- statement:
--   The PAdic Hodge construction uses the norm sub le max of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L321-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L321-L324

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.norm_sub_le_max_of_le {x b y : PadicAlgCl p} {s t : ℝ} (h1 : ‖x - b‖ ≤ s)
    (h2 : ‖b - y‖ ≤ t) : ‖x - y‖ ≤ max s t := by sorry
