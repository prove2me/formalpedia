-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_add
-- name    : GroundTheory.PAdicHodge.extendToClosure_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:20.306799+00:00
-- url     : https://prove2.me/theorems/5fa81190-8ffd-4b9c-aac5-4218cc31aa14
-- title:
--   PAdic Hodge: extend To Closure add
-- statement:
--   The PAdic Hodge construction uses the extend To Closure add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L166-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L166-L180

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

theorem GroundTheory.PAdicHodge.extendToClosure_add {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    x + x' ∈ closureInCp E ∧
      extendToClosure E R (x + x') = extendToClosure E R x + extendToClosure E R x' := by sorry
