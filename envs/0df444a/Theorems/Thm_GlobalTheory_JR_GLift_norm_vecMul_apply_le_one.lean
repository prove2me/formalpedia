-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLift_norm_vecMul_apply_le_one
-- name    : GlobalTheory.JR.GLift.norm_vecMul_apply_le_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:31:50.604642+00:00
-- url     : https://prove2.me/theorems/f45d719a-3ada-4304-bbde-a2d5ca5e5579
-- title:
--   GLift: norm vec Mul apply le one
-- statement:
--   The GLift construction uses the norm vec Mul apply le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockGlBorderedConjugationActionI.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockGlBorderedConjugationActionI.lean#L18-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockGlBorderedConjugationActionI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift

theorem GlobalTheory.JR.GLift.norm_vecMul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (v : Fin n → F) (A : Matrix (Fin n) (Fin n) F) (hv : ∀ i, ‖v i‖ ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (j : Fin n) : ‖(v ᵥ* A) j‖ ≤ 1 := by sorry
