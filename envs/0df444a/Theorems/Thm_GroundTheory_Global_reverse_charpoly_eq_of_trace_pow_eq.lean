-- Prove2me | Theorems.Thm_GroundTheory_Global_reverse_charpoly_eq_of_trace_pow_eq
-- name    : GroundTheory.Global.reverse_charpoly_eq_of_trace_pow_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:00.144348+00:00
-- url     : https://prove2.me/theorems/5394ff3c-49f5-448d-a583-0588d07af124
-- title:
--   Global: reverse charpoly eq of trace pow eq
-- statement:
--   The Global construction uses the reverse charpoly eq of trace pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L171-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L171-L197

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']

theorem GroundTheory.Global.reverse_charpoly_eq_of_trace_pow_eq [CharZero k] (A : Module.End k W)
    (B : Module.End k W')
    (h : ∀ m, 0 < m → LinearMap.trace k W (A ^ m) = LinearMap.trace k W' (B ^ m)) :
    A.charpoly.reverse = B.charpoly.reverse := by sorry
