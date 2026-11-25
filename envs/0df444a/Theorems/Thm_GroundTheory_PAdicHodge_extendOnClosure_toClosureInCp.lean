-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendOnClosure_toClosureInCp
-- name    : GroundTheory.PAdicHodge.extendOnClosure_toClosureInCp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:54.843607+00:00
-- url     : https://prove2.me/theorems/67aaead0-98b7-4b97-b547-e25042ccc6c5
-- title:
--   PAdic Hodge: extend On Closure to Closure In Cp
-- statement:
--   The PAdic Hodge construction uses the extend On Closure to Closure In Cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L109-L112

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

theorem GroundTheory.PAdicHodge.extendOnClosure_toClosureInCp (y : E) :
    extendOnClosure E R (toClosureInCp E y) = ((R y : PadicAlgCl p) : ℂ_[p]) := by sorry
