-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_gal_mem_unramifiedClosure
-- name    : GroundTheory.PAdicHodge.gal_mem_unramifiedClosure
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:39.106872+00:00
-- url     : https://prove2.me/theorems/680f9a28-344d-4304-a30b-52c7fed398de
-- title:
--   PAdic Hodge: gal mem unramified Closure
-- statement:
--   The PAdic Hodge construction uses the gal mem unramified Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L33-L41

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

theorem GroundTheory.PAdicHodge.gal_mem_unramifiedClosure (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p}
    (hx : x ∈ unramifiedClosure p) : τ x ∈ unramifiedClosure p := by sorry
