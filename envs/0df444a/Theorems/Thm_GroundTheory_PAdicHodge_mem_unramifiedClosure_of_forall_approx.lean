-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_unramifiedClosure_of_forall_approx
-- name    : GroundTheory.PAdicHodge.mem_unramifiedClosure_of_forall_approx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:52.210632+00:00
-- url     : https://prove2.me/theorems/507bed07-b395-4544-a32d-35815ea431cf
-- title:
--   PAdic Hodge: mem unramified Closure of forall approx
-- statement:
--   The PAdic Hodge construction uses the mem unramified Closure of forall approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L59-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L59-L77

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

theorem GroundTheory.PAdicHodge.mem_unramifiedClosure_of_forall_approx {β : PadicAlgCl p}
    (h : ∀ m : ℕ, ∃ u ∈ unramifiedClosure p, ‖β - u‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m) :
    β ∈ unramifiedClosure p := by sorry
