-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wordMap_permMat
-- name    : GlobalTheory.SmoothForms.PermWord.wordMap_permMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:57.734671+00:00
-- url     : https://prove2.me/theorems/0c03bb6a-704e-4d1a-a9a9-cfbfb650c63c
-- title:
--   Perm Word: word Map perm Mat
-- statement:
--   The Perm Word construction uses the word Map perm Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L206-L215

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

theorem GlobalTheory.SmoothForms.PermWord.wordMap_permMat {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) :
    wordMap E d (permMat n d π) = ∑ K : Fin d → Fin n, (List.ofFn fun a => E (K (π a)) (K a)).prod := by sorry
