-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_perm_sub_mem
-- name    : GlobalTheory.SmoothForms.PermWord.perm_sub_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:04.942732+00:00
-- url     : https://prove2.me/theorems/1872baea-9807-4630-a3cb-4893016370fe
-- title:
--   Perm Word: perm sub mem
-- statement:
--   The Perm Word construction uses the perm sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L134-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L134-L151

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

theorem GlobalTheory.SmoothForms.PermWord.perm_sub_mem {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    wd E l - wd E l' ∈ shorter E l.length := by sorry
