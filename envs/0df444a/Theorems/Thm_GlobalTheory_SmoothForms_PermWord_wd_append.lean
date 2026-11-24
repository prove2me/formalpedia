-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_append
-- name    : GlobalTheory.SmoothForms.PermWord.wd_append
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:50.99152+00:00
-- url     : https://prove2.me/theorems/f65c5a35-93aa-4651-99e2-f9bcfce6f22f
-- title:
--   Perm Word: wd append
-- statement:
--   The Perm Word construction uses the wd append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L89-L90

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

theorem GlobalTheory.SmoothForms.PermWord.wd_append {B : Type} [Ring B] (E : Fin n → Fin n → B) (l l' : List (Fin n × Fin n)) :
    wd E (l ++ l') = wd E l * wd E l' := by sorry
