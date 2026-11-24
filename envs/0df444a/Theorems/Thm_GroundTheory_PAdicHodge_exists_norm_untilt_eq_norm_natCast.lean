-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq_norm_natCast
-- name    : GroundTheory.PAdicHodge.exists_norm_untilt_eq_norm_natCast
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:31.461929+00:00
-- url     : https://prove2.me/theorems/1f6d86e9-3d76-4871-9a95-aad2b38c0b64
-- title:
--   PAdic Hodge: exists norm untilt eq norm nat Cast
-- statement:
--   The PAdic Hodge construction uses the exists norm untilt eq norm nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean#L296-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean#L296-L315

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
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
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.exists_norm_untilt_eq_norm_natCast :
    ∃ x : PreTilt (normInteger K) p, ‖((x.untilt : normInteger K) : K)‖ = ‖(p : K)‖ := by sorry
