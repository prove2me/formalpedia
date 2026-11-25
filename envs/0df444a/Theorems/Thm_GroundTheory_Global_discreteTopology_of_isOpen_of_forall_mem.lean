-- Prove2me | Theorems.Thm_GroundTheory_Global_discreteTopology_of_isOpen_of_forall_mem
-- name    : GroundTheory.Global.discreteTopology_of_isOpen_of_forall_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:30.369421+00:00
-- url     : https://prove2.me/theorems/f4c7715e-a06d-4fad-b661-583b2e714f3f
-- title:
--   Global: discrete Topology of is Open of forall mem
-- statement:
--   The Global construction uses the discrete Topology of is Open of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L8-L21

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing

theorem GroundTheory.Global.discreteTopology_of_isOpen_of_forall_mem {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U)
    (hH : ∀ x ∈ H, x ∈ U → x = 0) : DiscreteTopology H := by sorry
