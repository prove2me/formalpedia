-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_mul
-- name    : GroundTheory.PAdicHodge.extendToClosure_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:30.054908+00:00
-- url     : https://prove2.me/theorems/0ae51499-3bf2-4d64-a08b-825f8ff64685
-- title:
--   PAdic Hodge: extend To Closure mul
-- statement:
--   The PAdic Hodge construction uses the extend To Closure mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L223-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L223-L241

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
omit [FiniteDimensional ℚ_[p] k]
include hkE hmul

theorem GroundTheory.PAdicHodge.extendToClosure_mul {a : PadicAlgCl p} (ha : a ∈ k) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) :
    extendToClosure E R ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * extendToClosure E R x := by sorry
