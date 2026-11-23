-- Prove2me | Theorems.Thm_GlobalTheory_exists_orthonormal_frameMul_eq
-- name    : GlobalTheory.exists_orthonormal_frameMul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:40.195368+00:00
-- url     : https://prove2.me/theorems/bfb5994b-8d45-4baf-8439-45eb42fe77b3
-- title:
--   Global Theory: exists orthonormal frame Mul eq
-- statement:
--   The Global Theory construction uses the exists orthonormal frame Mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L177-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L177-L193

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

theorem GlobalTheory.exists_orthonormal_frameMul_eq (hV : ∀ s, finrank 𝕜 (V s) = r s)
    (x : ∀ s, Fin (r s) → V s) :
    ∃ (y : ∀ s, Fin (r s) → V s) (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜),
      (∀ s, Orthonormal 𝕜 (y s)) ∧ (∀ s, (b s).IsUpperTriangular) ∧
        (∀ s i, ‖b s i i‖ ≤ ‖x s i‖) ∧ frameMul y b = x := by sorry
