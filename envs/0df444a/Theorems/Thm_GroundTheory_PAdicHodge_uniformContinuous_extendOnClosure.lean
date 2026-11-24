-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_uniformContinuous_extendOnClosure
-- name    : GroundTheory.PAdicHodge.uniformContinuous_extendOnClosure
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:33.7938+00:00
-- url     : https://prove2.me/theorems/f1065094-8b46-4b5f-9a1e-27b9477fd247
-- title:
--   PAdic Hodge: uniform Continuous extend On Closure
-- statement:
--   The PAdic Hodge construction uses the uniform Continuous extend On Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L102-L104

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

theorem GroundTheory.PAdicHodge.uniformContinuous_extendOnClosure : UniformContinuous (extendOnClosure E R) := by sorry
