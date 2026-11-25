-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pow_totient
-- name    : GroundTheory.PAdicHodge.cyclRadius_pow_totient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:01.283581+00:00
-- url     : https://prove2.me/theorems/fd1f9746-c7e5-4d1a-82aa-e6afdcf2737c
-- title:
--   PAdic Hodge: cycl Radius pow totient
-- statement:
--   The PAdic Hodge construction uses the cycl Radius pow totient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L209-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L209-L212

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

theorem GroundTheory.PAdicHodge.cyclRadius_pow_totient (k : ℕ) :
    cyclRadius p (k + 1) ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by sorry
