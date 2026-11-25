-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_iota_injective
-- name    : GroundTheory.PAdicHodge.ACris.iota_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:45.940232+00:00
-- url     : https://prove2.me/theorems/033f5f2f-2aa4-4d05-97df-aeea01ea1bc8
-- title:
--   ACris: iota injective
-- statement:
--   The ACris construction uses the iota injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L109-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L109-L130

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
set_option maxHeartbeats 1600000

theorem GroundTheory.PAdicHodge.ACris.iota_injective : Function.Injective (iota K p) := by sorry
