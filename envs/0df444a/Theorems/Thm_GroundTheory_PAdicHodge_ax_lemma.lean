-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma
-- name    : GroundTheory.PAdicHodge.ax_lemma
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:48.819737+00:00
-- url     : https://prove2.me/theorems/e20ff1ec-068b-4da0-a108-5a8d135a2424
-- title:
--   PAdic Hodge: ax lemma
-- statement:
--   The PAdic Hodge construction uses the ax lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L449-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L449-L455

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
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.PAdicHodge.ax_lemma {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (x : PadicAlgCl p) {r : ℝ}
    (h : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ r) :
    ∃ y ∈ K, ‖x - y‖ ≤ axConstant p * r := by sorry
