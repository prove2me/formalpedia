-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateAlgebraLemmas_conjAlg_apply
-- name    : GlobalTheory.ConjugateAlgebraLemmas.conjAlg_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:13.574173+00:00
-- url     : https://prove2.me/theorems/74002891-df8c-4315-91bc-f4e911bc79b3
-- title:
--   Conjugate Algebra Lemmas: conj Alg apply
-- statement:
--   The Conjugate Algebra Lemmas construction uses the conj Alg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateAlgebraLemmas
open Matrix

theorem GlobalTheory.ConjugateAlgebraLemmas.conjAlg_apply {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    conjAlg g M = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) := by sorry
