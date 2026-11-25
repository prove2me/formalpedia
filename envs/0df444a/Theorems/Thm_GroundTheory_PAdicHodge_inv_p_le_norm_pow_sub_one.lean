-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_inv_p_le_norm_pow_sub_one
-- name    : GroundTheory.PAdicHodge.inv_p_le_norm_pow_sub_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:49.606527+00:00
-- url     : https://prove2.me/theorems/ff1266d8-1279-4514-89fe-39076253140d
-- title:
--   PAdic Hodge: inv p le norm pow sub one
-- statement:
--   The PAdic Hodge construction uses the inv p le norm pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L440-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L440-L455

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

theorem GroundTheory.PAdicHodge.inv_p_le_norm_pow_sub_one {ε : PadicAlgCl p} (hε : ε ^ p = 1) (hε1 : ε ≠ 1) {i : ℕ}
    (hi0 : 1 ≤ i) (hip : i < p) : (p : ℝ)⁻¹ ≤ ‖ε ^ i - 1‖ := by sorry
