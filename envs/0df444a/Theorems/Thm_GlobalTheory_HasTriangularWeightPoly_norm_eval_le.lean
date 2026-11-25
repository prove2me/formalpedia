-- Prove2me | Theorems.Thm_GlobalTheory_HasTriangularWeightPoly_norm_eval_le
-- name    : GlobalTheory.HasTriangularWeightPoly.norm_eval_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:21.847638+00:00
-- url     : https://prove2.me/theorems/f22e155e-3a57-57dc-a8b5-d262874ab105
-- title:
--   Has Triangular Weight Poly: norm eval le
-- statement:
--   The Has Triangular Weight Poly construction uses the norm eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L282-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L282-L307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]

theorem GlobalTheory.HasTriangularWeightPoly.norm_eval_le {a : ∀ s, Fin (r s) → ℕ}
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) 𝕜}
    (hp : HasTriangularWeightPoly a p) {C : ℝ}
    (hC : ∀ u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜,
      (∀ s, u s ∈ Matrix.unitaryGroup (Fin (r s)) 𝕜) → ‖MvPolynomial.eval (entries u) p‖ ≤ C)
    {R : ι → ℝ} (hR : ∀ s, 0 ≤ R s) {x : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜}
    (hx : ∀ s j, ∑ i, ‖x s i j‖ ^ 2 ≤ R s ^ 2) :
    ‖MvPolynomial.eval (entries x) p‖ ≤ C * ∏ s, R s ^ ∑ i, a s i := by sorry
