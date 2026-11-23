-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_le_max_of_ultrametric
-- name    : GroundTheory.PAdicHodge.norm_sub_le_max_of_ultrametric
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:13.769836+00:00
-- url     : https://prove2.me/theorems/dbde2c2c-098f-4d72-a7e8-aa54948b93ae
-- title:
--   PAdic Hodge: norm sub le max of ultrametric
-- statement:
--   The PAdic Hodge construction uses the norm sub le max of ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L54-L57

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

theorem GroundTheory.PAdicHodge.norm_sub_le_max_of_ultrametric {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] (a b : E) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry
