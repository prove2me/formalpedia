-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_maxUnramified
-- name    : GroundTheory.PAdicHodge.mem_maxUnramified
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:59.177863+00:00
-- url     : https://prove2.me/theorems/9147ea46-0928-59aa-8e1d-085cc2da6427
-- title:
--   PAdic Hodge: mem max Unramified
-- statement:
--   The PAdic Hodge construction uses the mem max Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L25-L27

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

theorem GroundTheory.PAdicHodge.mem_maxUnramified {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {x : PadicAlgCl p} :
    x ∈ maxUnramified p K ↔ x ∈ K ∧ x ∈ unramifiedClosure p := by sorry
