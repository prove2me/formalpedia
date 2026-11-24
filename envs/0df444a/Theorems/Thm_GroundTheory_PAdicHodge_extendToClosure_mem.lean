-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_mem
-- name    : GroundTheory.PAdicHodge.extendToClosure_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:33.583072+00:00
-- url     : https://prove2.me/theorems/39d858a7-83f1-44f0-87d0-2030006832ce
-- title:
--   PAdic Hodge: extend To Closure mem
-- statement:
--   The PAdic Hodge construction uses the extend To Closure mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L198-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L198-L202

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
variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] k]
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (hmul : ∀ a ∈ k, ∀ y ∈ E, R (a * y) = a * R y)
include hmaps

theorem GroundTheory.PAdicHodge.extendToClosure_mem {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R x ∈ ((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p)) := by sorry
