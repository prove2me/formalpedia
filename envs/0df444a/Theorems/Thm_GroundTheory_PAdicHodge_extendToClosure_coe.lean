-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_coe
-- name    : GroundTheory.PAdicHodge.extendToClosure_coe
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:51.810731+00:00
-- url     : https://prove2.me/theorems/fd03b14e-98a6-4470-be43-3ee89dcedd35
-- title:
--   PAdic Hodge: extend To Closure coe
-- statement:
--   The PAdic Hodge construction uses the extend To Closure coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L114-L117

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

theorem GroundTheory.PAdicHodge.extendToClosure_coe {y : PadicAlgCl p} (hy : y ∈ E) :
    extendToClosure E R (y : ℂ_[p]) = ((R y : PadicAlgCl p) : ℂ_[p]) := by sorry
