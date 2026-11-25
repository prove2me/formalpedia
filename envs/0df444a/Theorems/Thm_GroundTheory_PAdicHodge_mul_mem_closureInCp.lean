-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mul_mem_closureInCp
-- name    : GroundTheory.PAdicHodge.mul_mem_closureInCp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:53.440224+00:00
-- url     : https://prove2.me/theorems/24970046-57e1-4e8b-80ed-0f0067a446f9
-- title:
--   PAdic Hodge: mul mem closure In Cp
-- statement:
--   The PAdic Hodge construction uses the mul mem closure In Cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L214-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L214-L218

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
omit hadd hbound [FiniteDimensional ℚ_[p] k]
include hkE

theorem GroundTheory.PAdicHodge.mul_mem_closureInCp {a : PadicAlgCl p} (ha : a ∈ k) {x : ℂ_[p]}
    (hx : x ∈ closureInCp E) : (a : ℂ_[p]) * x ∈ closureInCp E := by sorry
