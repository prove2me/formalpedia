-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_one_le
-- name    : GroundTheory.PAdicHodge.norm_pow_sub_one_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:22.791356+00:00
-- url     : https://prove2.me/theorems/8b05bbca-741b-48f4-8817-d3934e7c6c22
-- title:
--   PAdic Hodge: norm pow sub one le
-- statement:
--   The PAdic Hodge construction uses the norm pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L23-L31

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

theorem GroundTheory.PAdicHodge.norm_pow_sub_one_le {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) (j : ℕ) :
    ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖ := by sorry
