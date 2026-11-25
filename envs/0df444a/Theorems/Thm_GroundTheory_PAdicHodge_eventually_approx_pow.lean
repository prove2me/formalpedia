-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_eventually_approx_pow
-- name    : GroundTheory.PAdicHodge.eventually_approx_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:31.564623+00:00
-- url     : https://prove2.me/theorems/b70ea323-f98a-48b7-8d06-23159d139ec4
-- title:
--   PAdic Hodge: eventually approx pow
-- statement:
--   The PAdic Hodge construction uses the eventually approx pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L224-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L224-L271

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

theorem GroundTheory.PAdicHodge.eventually_approx_pow {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (m : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ u ∈ unramifiedClosure p,
      ‖c ^ p ^ k - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by sorry
