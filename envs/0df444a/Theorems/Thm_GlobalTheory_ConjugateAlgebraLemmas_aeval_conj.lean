-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateAlgebraLemmas_aeval_conj
-- name    : GlobalTheory.ConjugateAlgebraLemmas.aeval_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:35.383591+00:00
-- url     : https://prove2.me/theorems/b4068207-2ffa-46b0-91c6-a5140c8205db
-- title:
--   Conjugate Algebra Lemmas: aeval conj
-- statement:
--   The Conjugate Algebra Lemmas construction uses the aeval conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L28-L33

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

theorem GlobalTheory.ConjugateAlgebraLemmas.aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : Polynomial K) :
    Polynomial.aeval ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) Q
      = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K) := by sorry
