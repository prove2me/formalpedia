-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_gal_apply_sub_le
-- name    : GroundTheory.PAdicHodge.norm_gal_apply_sub_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:29.591702+00:00
-- url     : https://prove2.me/theorems/932c4158-3bf8-4431-ad98-4a8574ab0c9d
-- title:
--   PAdic Hodge: norm gal apply sub le
-- statement:
--   The PAdic Hodge construction uses the norm gal apply sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L260-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L260-L269

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
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.norm_gal_apply_sub_le (x b : PadicAlgCl p) {ρ : ℝ}
    (hρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) (σ : Gal(PadicAlgCl p/K)) :
    ‖σ b - b‖ ≤ max ‖x - b‖ ρ := by sorry
