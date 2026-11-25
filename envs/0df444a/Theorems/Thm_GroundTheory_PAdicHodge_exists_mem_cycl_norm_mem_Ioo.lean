-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_mem_cycl_norm_mem_Ioo
-- name    : GroundTheory.PAdicHodge.exists_mem_cycl_norm_mem_Ioo
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:50.920202+00:00
-- url     : https://prove2.me/theorems/0e80cf0b-bfb9-4923-95b3-a1a238c1d5c2
-- title:
--   PAdic Hodge: exists mem cycl norm mem Ioo
-- statement:
--   The PAdic Hodge construction uses the exists mem cycl norm mem Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L228-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L228-L256

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
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
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.exists_mem_cycl_norm_mem_Ioo {r : ℝ} (hr : r < 1) :
    ∃ n, ∃ x ∈ cycl p n, r < ‖x‖ ∧ ‖x‖ < 1 := by sorry
