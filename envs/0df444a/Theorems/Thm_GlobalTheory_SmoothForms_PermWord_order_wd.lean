-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_order_wd
-- name    : GlobalTheory.SmoothForms.PermWord.order_wd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:53.663951+00:00
-- url     : https://prove2.me/theorems/afe53305-75e0-495c-b8b7-295d1bce308e
-- title:
--   Perm Word: order wd
-- statement:
--   The Perm Word construction uses the order wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L166-L169

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

theorem GlobalTheory.SmoothForms.PermWord.order_wd (E : Fin n → Fin n → A) (l : List (Fin n × Fin n)) :
    order E (wd (gen n) l) = wd E (l : Multiset (Fin n × Fin n)).toList := by sorry
