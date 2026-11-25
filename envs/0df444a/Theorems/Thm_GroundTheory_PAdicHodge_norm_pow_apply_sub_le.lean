-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_apply_sub_le
-- name    : GroundTheory.PAdicHodge.norm_pow_apply_sub_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:28.363194+00:00
-- url     : https://prove2.me/theorems/98a63054-f30c-426d-8dd7-0e3ed14bd87d
-- title:
--   PAdic Hodge: norm pow apply sub le
-- statement:
--   The PAdic Hodge construction uses the norm pow apply sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L414-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L414-L423

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

theorem GroundTheory.PAdicHodge.norm_pow_apply_sub_le (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p)
    (N : ℕ) : ‖(γ ^ N) y - y‖ ≤ ‖γ y - y‖ := by sorry
