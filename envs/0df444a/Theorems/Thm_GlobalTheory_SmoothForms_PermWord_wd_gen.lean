-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_gen
-- name    : GlobalTheory.SmoothForms.PermWord.wd_gen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:02.264612+00:00
-- url     : https://prove2.me/theorems/5bd5b65c-0d9d-4ec2-9411-aaf62ffb1df5
-- title:
--   Perm Word: wd gen
-- statement:
--   The Perm Word construction uses the wd gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L155-L161

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

theorem GlobalTheory.SmoothForms.PermWord.wd_gen (l : List (Fin n × Fin n)) :
    wd (gen n) l = MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset (Fin n × Fin n))) 1 := by sorry
