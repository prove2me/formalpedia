-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_totient_prime_pow_succ
-- name    : GroundTheory.PAdicHodge.totient_prime_pow_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:02.875921+00:00
-- url     : https://prove2.me/theorems/1dc355f6-66e3-45fd-8efd-13e70bc0dde0
-- title:
--   PAdic Hodge: totient prime pow succ
-- statement:
--   The PAdic Hodge construction uses the totient prime pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L148-L151

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

theorem GroundTheory.PAdicHodge.totient_prime_pow_succ {k : ℕ} (hk : 1 ≤ k) :
    Nat.totient (p ^ (k + 1)) = p * Nat.totient (p ^ k) := by sorry
