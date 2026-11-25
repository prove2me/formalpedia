-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_one_sub_pow_le
-- name    : GroundTheory.PAdicHodge.norm_one_sub_pow_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:15.665057+00:00
-- url     : https://prove2.me/theorems/423e1bd6-6948-4ef8-8371-960ff4c9ac14
-- title:
--   PAdic Hodge: norm one sub pow le
-- statement:
--   The PAdic Hodge construction uses the norm one sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
variable {F : Type*} [NormedField F] [IsUltrametricDist F]

theorem GroundTheory.PAdicHodge.norm_one_sub_pow_le {x : F} (hx : ‖x‖ ≤ 1) (m : ℕ) : ‖1 - x ^ m‖ ≤ ‖1 - x‖ := by sorry
