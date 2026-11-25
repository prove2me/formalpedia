-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_lipschitzWith_coe_comp
-- name    : GroundTheory.PAdicHodge.lipschitzWith_coe_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:24.123336+00:00
-- url     : https://prove2.me/theorems/8d93bed2-9d63-4cf0-bd51-cb5e311601b2
-- title:
--   PAdic Hodge: lipschitz With coe comp
-- statement:
--   The PAdic Hodge construction uses the lipschitz With coe comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L90-L96

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

theorem GroundTheory.PAdicHodge.lipschitzWith_coe_comp :
    LipschitzWith (Real.toNNReal c) fun y : E => ((R y : PadicAlgCl p) : ℂ_[p]) := by sorry
