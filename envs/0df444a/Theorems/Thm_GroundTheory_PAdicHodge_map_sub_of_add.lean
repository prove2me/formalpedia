-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_sub_of_add
-- name    : GroundTheory.PAdicHodge.map_sub_of_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:04.729499+00:00
-- url     : https://prove2.me/theorems/fe6e0b1f-14c7-42fa-93c6-40b9c1695947
-- title:
--   PAdic Hodge: map sub of add
-- statement:
--   The PAdic Hodge construction uses the map sub of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L82-L86

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (R : PadicAlgCl p → PadicAlgCl p)
variable {E R}
variable {c : ℝ} (hadd : ∀ y ∈ E, ∀ z ∈ E, R (y + z) = R y + R z)
  (hbound : ∀ y ∈ E, ‖R y‖ ≤ c * ‖y‖)
include hadd

theorem GroundTheory.PAdicHodge.map_sub_of_add {y z : PadicAlgCl p} (hy : y ∈ E) (hz : z ∈ E) :
    R (y - z) = R y - R z := by sorry
