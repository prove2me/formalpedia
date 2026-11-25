-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cycl_mul_le
-- name    : GroundTheory.PAdicHodge.norm_normTrace_cycl_mul_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:10.362918+00:00
-- url     : https://prove2.me/theorems/8ddb778a-472f-4557-ae2d-153b64eba06c
-- title:
--   PAdic Hodge: norm norm Trace cycl mul le
-- statement:
--   The PAdic Hodge construction uses the norm norm Trace cycl mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L381-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L381-L392

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
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
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.norm_normTrace_cycl_mul_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ cycl p m) :
    ‖normTrace (cycl p n) x‖ * cyclRadius p n ≤ ‖x‖ * cyclRadius p m := by sorry
