-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma_closedSubgroup
-- name    : GroundTheory.PAdicHodge.ax_lemma_closedSubgroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:36.080288+00:00
-- url     : https://prove2.me/theorems/c3fbaead-768a-449a-9a83-90eeb2c3fc71
-- title:
--   PAdic Hodge: ax lemma closed Subgroup
-- statement:
--   The PAdic Hodge construction uses the ax lemma closed Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L538-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L538-L558

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
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
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.ax_lemma_closedSubgroup (H : Subgroup Gal(PadicAlgCl p/K))
    (hH : IsClosed (H : Set Gal(PadicAlgCl p/K))) (z : PadicAlgCl p) {r : ℝ}
    (hz : ∀ σ ∈ H, ‖σ z - z‖ ≤ r) :
    ∃ y ∈ IntermediateField.fixedField H, ‖z - y‖ ≤ axConstant p * r := by sorry
