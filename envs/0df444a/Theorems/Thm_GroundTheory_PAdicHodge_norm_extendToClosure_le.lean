-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_extendToClosure_le
-- name    : GroundTheory.PAdicHodge.norm_extendToClosure_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:15.316287+00:00
-- url     : https://prove2.me/theorems/4e2650ba-8fae-417a-9d8a-3900cb4d149b
-- title:
--   PAdic Hodge: norm extend To Closure le
-- statement:
--   The PAdic Hodge construction uses the norm extend To Closure le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L182-L188

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
include hbound

theorem GroundTheory.PAdicHodge.norm_extendToClosure_le {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    ‖extendToClosure E R x‖ ≤ c * ‖x‖ := by sorry
