-- Prove2me | Theorems.Thm_GlobalTheory_annihilator_diagonal_trace
-- name    : GlobalTheory.annihilator_diagonal_trace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:39.689791+00:00
-- url     : https://prove2.me/theorems/ab6d08c7-bae9-47b1-91de-9fff50fdcc06
-- title:
--   Global Theory: annihilator diagonal trace
-- statement:
--   The Global Theory construction uses the annihilator diagonal trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrMulDetEqNormOfAnnihilator.lean#L24-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrMulDetEqNormOfAnnihilator.lean#L24-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped TensorProduct

theorem GlobalTheory.annihilator_diagonal_trace {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Module.Basis (Fin d) R B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0) :
    ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j = ∑ i, ∑ j, M i j • (b i * b j) := by sorry
