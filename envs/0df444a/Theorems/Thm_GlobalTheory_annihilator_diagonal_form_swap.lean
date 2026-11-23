-- Prove2me | Theorems.Thm_GlobalTheory_annihilator_diagonal_form_swap
-- name    : GlobalTheory.annihilator_diagonal_form_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:53.560801+00:00
-- url     : https://prove2.me/theorems/1f178241-3786-46af-8f75-2c11a9c47d49
-- title:
--   Global Theory: annihilator diagonal form swap
-- statement:
--   The Global Theory construction uses the annihilator diagonal form swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrMulDetEqNormOfAnnihilator.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrMulDetEqNormOfAnnihilator.lean#L7-L22

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

theorem GlobalTheory.annihilator_diagonal_form_swap {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Fin d → B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (f : B →ₗ[R] R) (y : B) :
    ∑ i, ∑ j, (M i j * f (b i * y)) • b j = ∑ i, ∑ j, (M i j * f (b i)) • (b j * y) := by sorry
