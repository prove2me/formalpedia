-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_self_le
-- name    : GroundTheory.PAdicHodge.norm_pow_sub_self_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:41.508818+00:00
-- url     : https://prove2.me/theorems/768c26c2-2de7-4fe4-93ad-b29378df9be8
-- title:
--   PAdic Hodge: norm pow sub self le
-- statement:
--   The PAdic Hodge construction uses the norm pow sub self le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L131-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L131-L141

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.norm_pow_sub_self_le {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : ‖c ^ p - c‖ ≤ (p : ℝ)⁻¹ := by sorry
