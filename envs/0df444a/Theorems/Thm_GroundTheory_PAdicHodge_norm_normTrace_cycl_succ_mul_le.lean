-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cycl_succ_mul_le
-- name    : GroundTheory.PAdicHodge.norm_normTrace_cycl_succ_mul_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:08.771146+00:00
-- url     : https://prove2.me/theorems/95287e39-9ae3-49aa-b6a8-7af15fbcddb9
-- title:
--   PAdic Hodge: norm norm Trace cycl succ mul le
-- statement:
--   The PAdic Hodge construction uses the norm norm Trace cycl succ mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L357-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L357-L379

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

theorem GroundTheory.PAdicHodge.norm_normTrace_cycl_succ_mul_le {k : ℕ} (hk : 1 ≤ k) {x : PadicAlgCl p}
    (hx : x ∈ cycl p (k + 1)) :
    ‖normTrace (cycl p k) x‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖x‖ := by sorry
