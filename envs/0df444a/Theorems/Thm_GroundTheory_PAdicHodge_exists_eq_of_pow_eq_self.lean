-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_of_pow_eq_self
-- name    : GroundTheory.PAdicHodge.exists_eq_of_pow_eq_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:32.314467+00:00
-- url     : https://prove2.me/theorems/5e25d3f3-daa6-4058-9873-02a7ac8a361c
-- title:
--   PAdic Hodge: exists eq of pow eq self
-- statement:
--   The PAdic Hodge construction uses the exists eq of pow eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L79-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L79-L110

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

theorem GroundTheory.PAdicHodge.exists_eq_of_pow_eq_self {ω : ℂ_[p]} {r : ℕ} (hr : 1 ≤ r) (h : ω ^ p ^ r = ω) :
    ∃ u ∈ unramifiedClosure p, (u : ℂ_[p]) = ω := by sorry
