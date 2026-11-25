-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_iotaM_eq_zero
-- name    : GroundTheory.PAdicHodge.ACris.iotaM_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:11.259674+00:00
-- url     : https://prove2.me/theorems/5e0df294-c39b-5f02-b7a6-26710acb8ac3
-- title:
--   ACris: iota M eq zero
-- statement:
--   The ACris construction uses the iota M eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L54-L58

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

theorem GroundTheory.PAdicHodge.ACris.iotaM_eq_zero {y : ACris K p} (hy : iota K p y = 0) (m : ℕ) : embedding₂ K p m y = 0 := by sorry
