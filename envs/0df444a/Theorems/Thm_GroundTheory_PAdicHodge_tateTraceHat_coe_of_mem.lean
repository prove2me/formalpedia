-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_tateTraceHat_coe_of_mem
-- name    : GroundTheory.PAdicHodge.tateTraceHat_coe_of_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:44.751581+00:00
-- url     : https://prove2.me/theorems/8300f04e-97e2-4655-9b2d-21401a0e2f60
-- title:
--   PAdic Hodge: tate Trace Hat coe of mem
-- statement:
--   The PAdic Hodge construction uses the tate Trace Hat coe of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L131-L134

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

theorem GroundTheory.PAdicHodge.tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a := by sorry
