-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_norm_eq_one_of_compactSpace
-- name    : GroundTheory.PAdicHodge.SenTateChar.norm_eq_one_of_compactSpace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:39.488826+00:00
-- url     : https://prove2.me/theorems/fd4e55c0-dcfe-4784-8796-fa403ae7a086
-- title:
--   Sen Tate Char: norm eq one of compact Space
-- statement:
--   The Sen Tate Char construction uses the norm eq one of compact Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharQp.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharQp.lean#L13-L38

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharQp
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
open GroundTheory.PAdicHodge.SenTateChar
variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

theorem GroundTheory.PAdicHodge.SenTateChar.norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by sorry
