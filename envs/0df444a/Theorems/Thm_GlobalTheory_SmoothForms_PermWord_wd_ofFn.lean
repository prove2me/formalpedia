-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_ofFn
-- name    : GlobalTheory.SmoothForms.PermWord.wd_ofFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:37.718342+00:00
-- url     : https://prove2.me/theorems/c2f1cd2d-8be4-49d4-b270-1c25fded2e79
-- title:
--   Perm Word: wd of Fn
-- statement:
--   The Perm Word construction uses the wd of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L95-L97

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

theorem GlobalTheory.SmoothForms.PermWord.wd_ofFn {B : Type} [Ring B] (E : Fin n → Fin n → B) {d : ℕ} (I K : Fin d → Fin n) :
    wd E (List.ofFn fun a => (I a, K a)) = (List.ofFn fun a => E (I a) (K a)).prod := by sorry
