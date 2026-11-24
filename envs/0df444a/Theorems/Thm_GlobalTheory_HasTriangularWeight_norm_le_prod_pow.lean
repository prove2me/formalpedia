-- Prove2me | Theorems.Thm_GlobalTheory_HasTriangularWeight_norm_le_prod_pow
-- name    : GlobalTheory.HasTriangularWeight.norm_le_prod_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:24.811597+00:00
-- url     : https://prove2.me/theorems/abfe895f-8185-4d3a-9ee1-b76a48676771
-- title:
--   Has Triangular Weight: norm le prod pow
-- statement:
--   The Has Triangular Weight construction uses the norm le prod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L206-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L206-L217

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
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]

theorem GlobalTheory.HasTriangularWeight.norm_le_prod_pow (hV : ∀ s, finrank 𝕜 (V s) = r s)
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (hc : Continuous P) {C : ℝ} (hC : ∀ y, (∀ s, Orthonormal 𝕜 (y s)) → ‖P y‖ ≤ C)
    {R : ι → ℝ} {x : ∀ s, Fin (r s) → V s} (hx : ∀ s i, ‖x s i‖ ≤ R s) :
    ‖P x‖ ≤ C * ∏ s, R s ^ ∑ i, a s i := by sorry
