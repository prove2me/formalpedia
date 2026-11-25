-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_mem_acrisZero_of_forall_dvd
-- name    : GroundTheory.PAdicHodge.ACris.mem_acrisZero_of_forall_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:59.806691+00:00
-- url     : https://prove2.me/theorems/522a4f54-912f-4eac-8a38-2f754fac229a
-- title:
--   ACris: mem acris Zero of forall dvd
-- statement:
--   The ACris construction uses the mem acris Zero of forall dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L19-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L19-L52

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

theorem GroundTheory.PAdicHodge.ACris.mem_acrisZero_of_forall_dvd {z : 𝔸}
    (h : ∀ m : ℕ, ∃ s ∈ ACrisZero K p, algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ z - s) :
    z ∈ ACrisZero K p := by sorry
