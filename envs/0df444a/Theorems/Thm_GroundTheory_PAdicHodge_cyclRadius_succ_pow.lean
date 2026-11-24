-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_succ_pow
-- name    : GroundTheory.PAdicHodge.cyclRadius_succ_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:15.247808+00:00
-- url     : https://prove2.me/theorems/2003de24-4c76-4ed5-ad3e-21ba242517f7
-- title:
--   PAdic Hodge: cycl Radius succ pow
-- statement:
--   The PAdic Hodge construction uses the cycl Radius succ pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L226-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L226-L233

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

theorem GroundTheory.PAdicHodge.cyclRadius_succ_pow {k : ℕ} (hk : 1 ≤ k) : cyclRadius p (k + 1) ^ p = cyclRadius p k := by sorry
