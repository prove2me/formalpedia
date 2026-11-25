-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_approx_of_pow_sub
-- name    : GroundTheory.PAdicHodge.exists_approx_of_pow_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:43.072911+00:00
-- url     : https://prove2.me/theorems/1a18ee0a-81be-4894-b581-af305c8ac4be
-- title:
--   PAdic Hodge: exists approx of pow sub
-- statement:
--   The PAdic Hodge construction uses the exists approx of pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L168-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L168-L218

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
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
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}

theorem GroundTheory.PAdicHodge.exists_approx_of_pow_sub {z : ℂ_[p]} (hz : ‖z‖ ≤ 1) {r m : ℕ} (hr : 1 ≤ r)
    (h : ‖z ^ p ^ r - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m) :
    ∃ u ∈ unramifiedClosure p, ‖z - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by sorry
