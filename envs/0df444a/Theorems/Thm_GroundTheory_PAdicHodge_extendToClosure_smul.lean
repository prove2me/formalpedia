-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_smul
-- name    : GroundTheory.PAdicHodge.extendToClosure_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:25.246211+00:00
-- url     : https://prove2.me/theorems/645fe9dc-4332-4fba-b58d-5de9b44a8c4e
-- title:
--   PAdic Hodge: extend To Closure smul
-- statement:
--   The PAdic Hodge construction uses the extend To Closure smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L257-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L257-L274

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
variable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.extendToClosure_smul (σ : Gal(PadicAlgCl p/K₀)) (hσ : ∀ y ∈ E, σ y ∈ E)
    (hσR : ∀ y ∈ E, R (σ y) = σ (R y)) {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R (σ • x) = σ • extendToClosure E R x := by sorry
