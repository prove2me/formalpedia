-- Prove2me | Theorems.Thm_GlobalTheory_HasTriangularWeight_norm_le_prod
-- name    : GlobalTheory.HasTriangularWeight.norm_le_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:16.043612+00:00
-- url     : https://prove2.me/theorems/4d54d10d-2a76-4740-a25e-d8bd9e650fd6
-- title:
--   Has Triangular Weight: norm le prod
-- statement:
--   The Has Triangular Weight construction uses the norm le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L195-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L195-L204

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

theorem GlobalTheory.HasTriangularWeight.norm_le_prod (hV : ∀ s, finrank 𝕜 (V s) = r s)
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (hc : Continuous P) {C : ℝ} (hC : ∀ y, (∀ s, Orthonormal 𝕜 (y s)) → ‖P y‖ ≤ C)
    (x : ∀ s, Fin (r s) → V s) : ‖P x‖ ≤ C * ∏ s, ∏ i, ‖x s i‖ ^ a s i := by sorry
