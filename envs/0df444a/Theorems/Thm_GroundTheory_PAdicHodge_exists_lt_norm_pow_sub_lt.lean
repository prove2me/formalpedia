-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_lt_norm_pow_sub_lt
-- name    : GroundTheory.PAdicHodge.exists_lt_norm_pow_sub_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:45.186289+00:00
-- url     : https://prove2.me/theorems/a48cc76d-5256-463c-bf3e-0a8ddd9ee70e
-- title:
--   PAdic Hodge: exists lt norm pow sub lt
-- statement:
--   The PAdic Hodge construction uses the exists lt norm pow sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L220-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L220-L222

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

theorem GroundTheory.PAdicHodge.exists_lt_norm_pow_sub_lt {c : PadicAlgCl p} (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (f : ℕ → ℕ) : ∃ k₀ k₁, k₀ < k₁ ∧ ‖c ^ f k₁ - c ^ f k₀‖ < ε := by sorry
