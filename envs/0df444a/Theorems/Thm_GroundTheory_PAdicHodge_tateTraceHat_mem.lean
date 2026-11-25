-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_mem
-- name    : GroundTheory.PAdicHodge.tateTraceHat_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:16.451261+00:00
-- url     : https://prove2.me/theorems/468d275b-3031-477d-9665-5d695c7d422c
-- title:
--   PAdic Hodge: tate Trace Hat mem
-- statement:
--   The PAdic Hodge construction uses the tate Trace Hat mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L125-L129

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
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
open IntermediateField Module Set
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]
variable {K}

theorem GroundTheory.PAdicHodge.tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) := by sorry
