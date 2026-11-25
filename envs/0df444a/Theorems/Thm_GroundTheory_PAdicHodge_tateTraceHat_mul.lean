-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_mul
-- name    : GroundTheory.PAdicHodge.tateTraceHat_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:41.25061+00:00
-- url     : https://prove2.me/theorems/4097f018-125e-5074-840d-cfc54b900753
-- title:
--   PAdic Hodge: tate Trace Hat mul
-- statement:
--   The PAdic Hodge construction uses the tate Trace Hat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L136-L140

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

theorem GroundTheory.PAdicHodge.tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x := by sorry
