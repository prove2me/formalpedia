-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_unramifiedClosure_of_pow_eq_one
-- name    : GroundTheory.PAdicHodge.mem_unramifiedClosure_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:28.389647+00:00
-- url     : https://prove2.me/theorems/33c62980-d00a-478d-9c04-4ab028cc0e8b
-- title:
--   PAdic Hodge: mem unramified Closure of pow eq one
-- statement:
--   The PAdic Hodge construction uses the mem unramified Closure of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L29-L31

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

theorem GroundTheory.PAdicHodge.mem_unramifiedClosure_of_pow_eq_one {x : PadicAlgCl p} {m : ℕ} (hm : 0 < m)
    (hc : m.Coprime p) (hx : x ^ m = 1) : x ∈ unramifiedClosure p := by sorry
