-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_shorter_le_filt
-- name    : GlobalTheory.SmoothForms.PermWord.shorter_le_filt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:39.112665+00:00
-- url     : https://prove2.me/theorems/80c88591-6b9f-46d9-9cf9-8e341df4ff11
-- title:
--   Perm Word: shorter le filt
-- statement:
--   The Perm Word construction uses the shorter le filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L105-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L105-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem GlobalTheory.SmoothForms.PermWord.shorter_le_filt (E : Fin n → Fin n → A) (d : ℕ) : shorter E d ≤ filt E d := by sorry
